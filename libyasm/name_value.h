#ifndef YASM_NAME_VALUE_H
#define YASM_NAME_VALUE_H
///
/// @file libyasm/name_value.h
/// @brief YASM name/value interface.
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
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include <boost/noncopyable.hpp>
#include <boost/scoped_ptr.hpp>


namespace yasm {

class Expr;
class Object;

/// Name/value pair.
class NameValue : private boost::noncopyable {
public:
    /// Identifier value constructor.
    /// @param name         name; may be empty string if no name
    /// @param id           identifier value
    /// @param id_prefix    identifier prefix for raw identifiers
    NameValue(const std::string& name, const std::string& id, char id_prefix);

    /// String value constructor.
    /// @param name         name; may be empty string if no name
    /// @param str          string value
    NameValue(const std::string& name, const std::string& str);

    /// Expression value constructor.
    /// @param name         name; may be empty string if no name
    /// @param e            expression
    NameValue(const std::string& name, std::auto_ptr<Expr> e);

    /// Identifier value constructor with no name.
    /// @param id           identifier value
    /// @param id_prefix    identifier prefix for raw identifiers
    NameValue(const std::string& id, char id_prefix);

    /// String value constructor with no name.
    /// @param name         name; may be empty string if no name
    /// @param str          string value
    NameValue(const std::string& str);

    /// Expression value constructor with no name.
    /// @param e            expression
    NameValue(std::auto_ptr<Expr> e);

    /// Destructor.
    ~NameValue();

    /// Get name.
    /// @return Name; empty string if no name.
    std::string get_name() const { return m_name; }

    /// Determine if value is convertible to an expression using get_expr().
    /// @return True if convertible.
    bool is_expr() const { return (m_type == ID) || (m_type == EXPR); }

    /// Determine if value is convertible to a string using get_string().
    /// @return True if convertible.
    bool is_string() const { return (m_type == ID) || (m_type == STRING); }

    /// Determine if value is convertible to an identifier using get_id().
    /// @return True if convertible.
    bool is_id() const { return m_type == ID; }

    /// Get value as an expr.  If the parameter is an identifier,
    /// it's treated as a symbol (Symbol::use() is called to convert it).
    /// @param object       object
    /// @param line         virtual line
    /// @return Expression, or NULL if the parameter cannot be
    ///         converted to an expression.
    /*@null@*/ std::auto_ptr<Expr> get_expr
        (Object& object, unsigned long line) const;

    /// Get value as a string.  If the parameter is an identifier,
    /// it's treated as a string.
    /// @return String; raises an exception if the parameter cannot be
    ///         realized as a string.
    std::string get_string() const;

    /// Get value as an identifier.
    /// @return Identifier (string); raises an exception if the parameter
    ///         is not an identifier.
    std::string get_id() const;

private:
    std::string m_name; ///< Name (empty string if no name)

    /// Value type.
    enum Type {
        ID,             ///< Identifier
        STRING,         ///< String
        EXPR            ///< Expression
    };

    Type m_type;

    /// Possible values
    std::string m_idstr;            ///< Identifier or string
    boost::scoped_ptr<Expr> m_expr; ///< Expression

    /// Prefix character that indicates a raw identifier.  When
    /// get_string() is called on a #ID, all characters are
    /// returned.  When get_id() is called on a #ID, if the
    /// identifier begins with this character, this character is stripped
    /// from the returned value.
    char m_id_prefix;
};

/// Vector of name/values.
typedef std::vector<NameValue> NameValues;

/// Print vector of name/values.  For debugging purposes.
/// @param os       output stream
/// @param namevals name/values
std::ostream& operator<< (std::ostream& os, const NameValues& namevals);

} // namespace yasm

#endif