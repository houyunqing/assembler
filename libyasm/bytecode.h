#ifndef YASM_BYTECODE_H
#define YASM_BYTECODE_H
///
/// @file libyasm/bytecode.h
/// @brief YASM bytecode interface.
///
/// @license
///  Copyright (C) 2001-2007  Peter Johnson
///
/// Redistribution and use in source and binary forms, with or without
/// modification, are permitted provided that the following conditions
/// are met:
///  - Redistributions of source code must retain the above copyright
///    notice, this list of conditions and the following disclaimer.
///  - Redistributions in binary form must reproduce the above copyright
///    notice, this list of conditions and the following disclaimer in the
///    documentation and/or other materials provided with the distribution.
///
/// THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND OTHER CONTRIBUTORS ``AS IS''
/// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
/// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
/// ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR OTHER CONTRIBUTORS BE
/// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
/// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
/// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
/// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
/// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
/// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
/// POSSIBILITY OF SUCH DAMAGE.
/// @endlicense
///
#include <iosfwd>
#include <memory>
#include <vector>

#include "functional.h"
#include <boost/noncopyable.hpp>
#include <boost/scoped_ptr.hpp>

#include "location.h"


namespace yasm {

class Arch;
class Bytecode;
class Bytes;
class Errwarns;
class Expr;
class Includes;
class Insn;
class IntNum;
class Linemap;
class Section;
class Symbol;
class Value;

/// Convert yasm_value to its byte representation.  Usually implemented by
/// object formats to keep track of relocations and verify legal expressions.
/// Must put the value into the least significant bits of the destination,
/// unless shifted into more significant bits by the shift parameter.  The
/// destination bits must be cleared before being set.  May raise an exception
/// if an error occurs.
/// @param value        value
/// @param bytes        storage for byte representation
/// @param destsize     destination size (in bytes)
/// @param loc          location of the expr contents (needed for relative)
/// @param warn         enables standard warnings.  Zero for none; nonzero
///                     for overflow/underflow floating point warnings;
///                     negative for signed integer warnings,
///                     positive for unsigned integer warnings
typedef
    FUNCTION::function<void (Value& value, Bytes& bytes, unsigned int destsize,
                             Location loc, int warn)>
    OutputValueFunc;

/// Convert a symbol reference to its byte representation.  Usually
/// implemented by object formats and debug formats to keep track of
/// relocations generated by themselves.  May raise an exception if an error
/// occurs.
/// @param sym          symbol
/// @param bc           current bytecode (usually passed into higher-level
///                     calling function)
/// @param bytes        storage for byte representation
/// @param destsize     destination size (in bytes)
/// @param valsize      size (in bits)
/// @param warn         enables standard warnings.  Zero for none; nonzero
///                     for overflow/underflow floating point warnings;
///                     negative for signed integer warnings,
///                     positive for unsigned integer warnings
typedef
    FUNCTION::function<void (Symbol* sym, Bytecode& bc, Bytes& bytes,
                             unsigned int destsize, unsigned int valsize,
                             int warn)>
    OutputRelocFunc;

/// A data value.
class Dataval {
public:
    /// Create a new data value from an expression.
    /// @param expn  expression
    Dataval(std::auto_ptr<Expr> expn);

    /// Create a new data value from a string.
    /// @param contents     string (may contain NULs)
    /// @param len          length of string
    Dataval(const std::string& str, size_t len);

    /// Create a new data value from raw bytes data.
    /// @param contents     raw data (may contain NULs)
    /// @param len          length
    Dataval(std::auto_ptr<unsigned char> contents, unsigned long len);
};


/// A bytecode.
class Bytecode {
    friend class Section;

public:
    /// Add a dependent span for a bytecode.
    /// @param bc           bytecode containing span
    /// @param id           non-zero identifier for span; may be any
    ///                     non-zero value
    ///                     if <0, expand is called for any change;
    ///                     if >0, expand is only called when exceeds
    ///                     threshold
    /// @param value        dependent value for bytecode expansion
    /// @param neg_thres    negative threshold for long/short decision
    /// @param pos_thres    positive threshold for long/short decision
    typedef
        FUNCTION::function<void (Bytecode& bc, int id, const Value& value,
                                 long neg_thres, long pos_thres)>
        AddSpanFunc;

    typedef std::auto_ptr<Bytecode> Ptr;

    /// Bytecode contents (abstract base class).  Any implementation of a
    /// specific bytecode must implement a class derived from this one.
    /// The bytecode implementation-specific data is stored in #contents.
    class Contents {
    public:
        typedef std::auto_ptr<Contents> Ptr;

        Contents() {}
        virtual ~Contents() {}

        /// Prints the implementation-specific data (for debugging purposes).
        /// Called from Bytecode::put().
        /// @param os           output stream
        /// @param indent_level indentation level
        virtual void put(std::ostream& os, int indent_level) const = 0;

        /// Finalizes the bytecode after parsing.
        /// Called from Bytecode::finalize().
        /// @param bc           bytecode
        virtual void finalize(Bytecode& bc) = 0;

        /// Calculates the minimum size of a bytecode.
        /// Called from Bytecode::calc_len().
        /// The base version of this function internal errors when called,
        /// so be very careful using the base function in a derived class!
        ///
        /// @param bc           bytecode
        /// @param add_span     function to call to add a span
        /// @return Length in bytes.
        /// @note May store to bytecode updated expressions.
        virtual unsigned long calc_len(Bytecode& bc,
                                       Bytecode::AddSpanFunc add_span) = 0;

        /// Recalculates the bytecode's length based on an expanded span
        /// length.  Called from Bytecode::expand().
        /// The base version of this function internal errors when called,
        /// so if used from a derived class, make sure that calc_len() never
        /// adds a span.
        /// This function should simply add to the len parameter to increase the
        /// length by a delta amount.
        /// @param bc           bytecode
        /// @param len          length (update this)
        /// @param span         span ID (as given to add_span in calc_len)
        /// @param old_val      previous span value
        /// @param new_val      new span value
        /// @param neg_thres    negative threshold for long/short decision
        ///                     (returned)
        /// @param pos_thres    positive threshold for long/short decision
        ///                     (returned)
        /// @return False if bc no longer dependent on this span's length,
        ///         or true if bc size may increase for this span further
        ///         based on the new negative and positive thresholds
        ///         returned.
        /// @note May store to bytecode updated expressions.
        virtual bool expand(Bytecode& bc, unsigned long& len, int span,
                            long old_val, long new_val,
                            /*@out@*/ long& neg_thres,
                            /*@out@*/ long& pos_thres) = 0;

        /// Convert a bytecode into its byte representation.
        /// Called from Bytecode::to_bytes().
        /// The base version of this function internal errors when called,
        /// so be very careful using the base function in a derived class!
        /// @param bc           bytecode
        /// @param bytes        byte representation destination buffer;
        ///                     on return, its size should match the bytecode
        ///                     length (it's okay not to do this if an error
        ///                     is thrown)
        /// @param output_value function to call to convert values into
        ///                     their byte representation
        /// @param output_reloc function to call to output relocation entries
        ///                     for a single sym
        /// @note May result in non-reversible changes to the bytecode, but
        ///       it's preferable if calling this function twice would result
        ///       in the same output.
        virtual void to_bytes(Bytecode& bc, Bytes& bytes,
                              OutputValueFunc output_value,
                              OutputRelocFunc output_reloc = 0) = 0;

        /// Get the number of items and itemsize for a reserve bytecode.
        /// Default implementation returns NULL; reserve bytecodes should
        /// implement this function.
        /// @param itemsize     reserved size (in bytes) for each item
        ///                     (returned)
        /// @return NULL if bc is not a reserve bytecode, otherwise an
        ///         expression for the number of items to reserve.
        virtual /*@null@*/ const Expr* reserve_numitems
            (/*@out@*/ unsigned int& itemsize) const;

        /// Special bytecode classifications.  Most bytecode types should
        /// simply not override the get_special() function (which returns
        /// #SPECIAL_NONE).  Other return values cause special handling to
        /// kick in in various parts of yasm.
        enum SpecialType {
            /// No special handling.
            SPECIAL_NONE = 0,

            /// Bytecode reserves space instead of outputting data.
            SPECIAL_RESERVE,

            /// Adjusts offset instead of calculating len.
            SPECIAL_OFFSET,

            /// Instruction bytecode.
            SPECIAL_INSN
        };

        virtual SpecialType get_special() const;

        virtual Contents* clone() const = 0;

    protected:
        /// Copy constructor so that derived classes can sanely have one.
        Contents(const Contents&) {}

    private:
        const Contents& operator=(const Contents&);
    };

    /// Create a bytecode of given contents.
    /// @param contents     type-specific data
    /// @param line         virtual line (from Linemap)
    Bytecode(Contents::Ptr contents, unsigned long line);

    /// Create a bytecode of no type.
    /// Caution: the bytecode will be unusable until it is transformed.
    Bytecode();

    Bytecode(const Bytecode& oth);
    Bytecode& operator= (const Bytecode& oth);

    /// Transform a bytecode of any type into a different type.
    /// @param contents     new type-specific data
    void transform(Contents::Ptr contents);

    /// Return if bytecode has contents.
    /// @return True if bytecode has contents.
    bool has_contents() const { return m_contents.get() != 0; }

    /// Set line number of bytecode.
    /// @param line     virtual line (from Linemap)
    void set_line(unsigned long line) { m_line = line; }

    /// Set multiple field of a bytecode.
    /// A bytecode can be repeated a number of times when output.  This
    /// function sets that multiple.
    /// @param e    multiple (kept, do not free)
    void set_multiple(std::auto_ptr<Expr> e);

    /// Multiply into the current multiple field.
    /// @param e    multiple (kept, do not free)
    void multiply_multiple(std::auto_ptr<Expr> e);

    /// Get the section that contains a particular bytecode.
    /// @param bc   bytecode
    /// @return Section containing bc (can be NULL if bytecode is not part of
    ///         a section).
    /*@dependent@*/ /*@null@*/ Section* get_section() const
    { return m_section; }

    /// Add to the list of symbols that reference a bytecode.
    /// @note Intended for #Symbol use only.
    /// @param sym  symbol
    void add_symbol(/*@dependent@*/ Symbol* sym) { m_symbols.push_back(sym); }

    /// Destructor.
    ~Bytecode();

    /// Print a bytecode.  For debugging purposes.
    /// @param os           output stream
    /// @param indent_level indentation level
    void put(std::ostream& os, int indent_level) const;

    /// Finalize a bytecode after parsing.
    void finalize();
    void finalize(Errwarns& errwarns);

    /// Get the offset of the bytecode.
    /// @return Offset of the bytecode in bytes.
    /// @warning Only valid /after/ optimization.
    unsigned long get_offset() const { return m_offset; }

    /// Set the offset of the bytecode.
    /// @internal Should be used by Object::optimize() only.
    /// @param offset       new offset of the bytecode
    void set_offset(unsigned long offset) { m_offset = offset; }

    /// Get the offset of the next bytecode (the next bytecode doesn't have to
    /// actually exist).
    /// @return Offset of the next bytecode in bytes.
    /// @warning Only valid /after/ optimization.
    unsigned long next_offset() const
    { return m_offset + m_len * m_mult_int; }

    /// Get the total length of the bytecode, including any multiples.
    /// @return Total length of the bytecode in bytes.
    /// @warning Only valid /after/ optimization.
    unsigned long get_total_len() const { return m_len * m_mult_int; }

    /// Get the basic length of the bytecode, excluding multiples.
    /// @return Length of the bytecode in bytes.
    /// @warning Only valid /after/ optimization.
    unsigned long get_len() const { return m_len; }

    /// Resolve EQUs in a bytecode and calculate its minimum size.
    /// Generates dependent bytecode spans for cases where, if the length
    /// spanned increases, it could cause the bytecode size to increase.
    /// Any bytecode multiple is NOT included in the length or spans
    /// generation; this must be handled at a higher level.
    /// @param add_span     function to call to add a span
    /// @note May store to bytecode updated expressions and the short length.
    void calc_len(AddSpanFunc add_span);
    void calc_len(AddSpanFunc add_span, Errwarns& errwarns);

    /// Recalculate a bytecode's length based on an expanded span length.
    /// @param span         span ID (as given to yasm_bc_add_span_func in
    ///                     yasm_bc_calc_len)
    /// @param old_val      previous span value
    /// @param new_val      new span value
    /// @param neg_thres    negative threshold for long/short decision
    ///                     (returned)
    /// @param pos_thres    positive threshold for long/short decision
    ///                     (returned)
    /// @return False if bc no longer dependent on this span's length,
    ///         or true if bc size may increase for this span further
    ///         based on the new negative and positive thresholds returned.
    /// @note May store to bytecode updated expressions and the updated
    ///       length.
    bool expand(int span, long old_val, long new_val,
                /*@out@*/ long& neg_thres, /*@out@*/ long& pos_thres);
    bool expand(int span, long old_val, long new_val,
                /*@out@*/ long& neg_thres, /*@out@*/ long& pos_thres,
                Errwarns& errwarns);

    /// Convert a bytecode into its byte representation.
    /// @param bc           bytecode
    /// @param bytes        byte representation destination
    /// @param gap          if nonzero: the data does not really need to
    ///                     exist in the object file, the value indicates
    ///                     the size to be reserved, and contents of bytes
    ///                     is undefined [output]
    /// @param output_value function to call to convert values into their
    ///                     byte representation
    /// @param output_reloc function to call to output relocation entries
    ///                     for a single sym
    /// @note Calling twice on the same bytecode may \em not produce the same
    ///       results on the second call, as calling this function may result
    ///       in non-reversible changes to the bytecode.
    void to_bytes(Bytes& bytes, /*@out@*/ unsigned long& gap,
                  OutputValueFunc output_value,
                  /*@null@*/ OutputRelocFunc output_reloc = 0);

    /// Get the bytecode multiple value as an integer.
    /// @param calc_dist True if distances between bytecodes should be
    ///                  calculated, false if error should be returned
    ///                  in this case
    /// @return Multiple value.
    long get_multiple(bool calc_dist);

    /// Get the bytecode multiple value as an expression.
    /// @return Bytecode multiple, NULL if =1.
    const Expr* get_multiple_expr() const
    { return m_multiple.get(); };

    /// Get the number of items and itemsize for a reserve bytecode.  If bc
    /// is not a reserve bytecode, returns NULL.
    /// @param bc           bytecode
    /// @param itemsize     reserved size (in bytes) for each item (returned)
    /// @return NULL if bc is not a reserve bytecode, otherwise an expression
    ///         for the number of items to reserve.
    /*@null@*/ const Expr* reserve_numitems
        (/*@out@*/ unsigned int& itemsize) const
    {
        if (m_contents.get() == 0)
            return 0;
        return m_contents->reserve_numitems(itemsize);
    }

    /// Get a #Insn structure from an instruction bytecode (if possible).
    /// @param bc           bytecode
    /// @return Instruction details if bytecode is an instruction bytecode,
    ///         otherwise NULL.
    /*@dependent@*/ /*@null@*/ Insn* get_insn() const;

    /// Updates bytecode offset.
    /// @note For offset-based bytecodes, calls expand() to determine new
    ///       length.
    /// @param offset       offset to set this bytecode to
    /// @param errwarns     error/warning set
    /// @return Offset of next bytecode.
    unsigned long update_offset(unsigned long offset);
    unsigned long update_offset(unsigned long offset, Errwarns& errwarns);

    unsigned long get_line() const { return m_line; }

    unsigned long get_index() const { return m_index; }
    void set_index(unsigned long idx) { m_index = idx; }

    Contents::SpecialType get_special() const
    {
        if (m_contents.get() == 0)
            return Contents::SPECIAL_NONE;
        return m_contents->get_special();
    }

private:
    /// Implementation-specific data.
    boost::scoped_ptr<Contents> m_contents;

    /// Pointer to section containing bytecode; NULL if not part of a
    /// section.
    /*@dependent@*/ /*@null@*/ Section* m_section;

    /// Number of times bytecode is repeated.
    /// NULL=1 (to save space in the common case).
    std::auto_ptr<Expr> m_multiple;

    /// Total length of entire bytecode (not including multiple copies).
    unsigned long m_len;

    /// Number of copies, integer version.
    long m_mult_int;

    /// Line number where bytecode was defined.
    unsigned long m_line;

    /// Offset of bytecode from beginning of its section.
    /// 0-based, ~0UL (e.g. all 1 bits) if unknown.
    unsigned long m_offset;

    /// Unique integer index of bytecode.  Used during optimization.
    unsigned long m_index;

    /// Labels that point to this bytecode (as the
    /// bytecode previous to the label).
    std::vector<Symbol*> m_symbols;
};

//
// General bytecode factory functions
//

/// Create a bytecode containing data value(s).
/// @param data         vector of data values
/// @param size         storage size (in bytes) for each data value
/// @param append_zero  append a single zero byte after each data value
///                     (if non-zero)
/// @param arch         architecture (optional); if provided, data items
///                     are directly simplified to bytes if possible
/// @param line         virtual line (from yasm_linemap)
/// @return Newly allocated bytecode.
std::auto_ptr<Bytecode> create_data
    (const std::vector<Dataval>& data, unsigned int size, int append_zero,
     /*@null@*/ Arch* arch, unsigned long line);

/// Create a bytecode containing LEB128-encoded data value(s).
/// @param datahead     list of data values (kept, do not free)
/// @param sign         signedness (True=signed, False=unsigned) of each
///                     data value
/// @param line         virtual line (from yasm_linemap)
/// @return Newly allocated bytecode.
std::auto_ptr<Bytecode> create_leb128
    (const std::vector<Dataval>& datahead, bool sign, unsigned long line);

/// Create a bytecode reserving space.
/// @param numitems     number of reserve "items" (kept, do not free)
/// @param itemsize     reserved size (in bytes) for each item
/// @param line         virtual line (from yasm_linemap)
/// @return Newly allocated bytecode contents.
Bytecode::Contents::Ptr create_reserve
    (std::auto_ptr<Expr> numitems, unsigned int itemsize);

/// Create a bytecode that includes a binary file verbatim.
/// @param filename     path to binary file
/// @param start        starting location in file (in bytes) to read data
///                     from (kept, do not free); may be NULL to indicate
///                     0
/// @param maxlen       maximum number of bytes to read from the file
///                     (kept, do not free); may be NULL to indicate no
///                     maximum
/// @param linemap      line mapping repository
/// @param line         virtual line (from linemap) for the bytecode
/// @return Newly allocated bytecode.
std::auto_ptr<Bytecode> create_incbin
    (const std::string& filename, /*@null@*/ std::auto_ptr<Expr> start,
     /*@null@*/ std::auto_ptr<Expr> maxlen, const Linemap& linemap,
     const Includes& includes, unsigned long line);

/// Create a bytecode that aligns the following bytecode to a boundary.
/// @param boundary     byte alignment (must be a power of two)
/// @param fill         fill data (if NULL, code_fill or 0 is used)
/// @param maxskip      maximum number of bytes to skip
/// @param code_fill    code fill data (if NULL, 0 is used)
/// @param line         virtual line (from yasm_linemap)
/// @return Newly allocated bytecode.
/// @note The precedence on generated fill is as follows:
///       - from fill parameter (if not NULL)
///       - from code_fill parameter (if not NULL)
///       - 0
std::auto_ptr<Bytecode> create_align
    (std::auto_ptr<Expr> boundary,
     /*@null@*/ std::auto_ptr<Expr> fill,
     /*@null@*/ std::auto_ptr<Expr> maxskip,
     /*@null@*/ const unsigned char** code_fill,
     unsigned long line);

/// Create a bytecode that puts the following bytecode at a fixed section
/// offset.
/// @param start        section offset of following bytecode
/// @param fill         fill value
/// @param line         virtual line (from yasm_linemap)
/// @return Newly allocated bytecode.
std::auto_ptr<Bytecode> create_org(unsigned long start, unsigned long fill,
                                   unsigned long line);

} // namespace yasm

#endif
