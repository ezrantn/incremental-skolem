//! Minimal S-expression tokenizer/parser. SMT-LIB2 is just parenthesized
//! symbols underneath, so this layer knows nothing about SMT-LIB
//! semantics -- that's `smt2.rs`'s job.

#[derive(Debug, Clone, PartialEq)]
pub enum Sexpr {
    Atom(String),
    List(Vec<Sexpr>),
}

impl Sexpr {
    pub fn atom(&self) -> Option<&str> {
        match self {
            Sexpr::Atom(s) => Some(s),
            Sexpr::List(_) => None,
        }
    }

    pub fn list(&self) -> Option<&[Sexpr]> {
        match self {
            Sexpr::List(items) => Some(items),
            Sexpr::Atom(_) => None,
        }
    }
}

#[derive(Debug)]
pub struct ParseError(pub String);

/// Tokenize and parse an entire SMT-LIB2 source string into a sequence of
/// top-level S-expressions (one per command, typically).
pub fn parse_all(src: &str) -> Result<Vec<Sexpr>, ParseError> {
    let tokens = tokenize(src);
    let mut pos = 0;
    let mut out = Vec::new();
    while pos < tokens.len() {
        let (expr, next) = parse_one(&tokens, pos)?;
        out.push(expr);
        pos = next;
    }
    Ok(out)
}

fn tokenize(src: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut chars = src.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            ';' => {
                // line comment
                while let Some(&c2) = chars.peek() {
                    if c2 == '\n' {
                        break;
                    }
                    chars.next();
                }
            }
            '(' | ')' => {
                tokens.push(c.to_string());
                chars.next();
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            '|' => {
                // quoted symbol: |...| verbatim until closing bar
                let mut s = String::new();
                s.push(chars.next().unwrap());
                for c2 in chars.by_ref() {
                    s.push(c2);
                    if c2 == '|' {
                        break;
                    }
                }
                tokens.push(s);
            }
            '"' => {
                // string literal
                let mut s = String::new();
                s.push(chars.next().unwrap());
                for c2 in chars.by_ref() {
                    s.push(c2);
                    if c2 == '"' {
                        break;
                    }
                }
                tokens.push(s);
            }
            _ => {
                let mut s = String::new();
                while let Some(&c2) = chars.peek() {
                    if c2 == '(' || c2 == ')' || c2.is_whitespace() {
                        break;
                    }
                    s.push(c2);
                    chars.next();
                }
                tokens.push(s);
            }
        }
    }
    tokens
}

fn parse_one(tokens: &[String], pos: usize) -> Result<(Sexpr, usize), ParseError> {
    if pos >= tokens.len() {
        return Err(ParseError("unexpected end of input".to_string()));
    }
    match tokens[pos].as_str() {
        "(" => {
            let mut items = Vec::new();
            let mut p = pos + 1;
            loop {
                if p >= tokens.len() {
                    return Err(ParseError("unclosed '('".to_string()));
                }
                if tokens[p] == ")" {
                    return Ok((Sexpr::List(items), p + 1));
                }
                let (item, next) = parse_one(tokens, p)?;
                items.push(item);
                p = next;
            }
        }
        ")" => Err(ParseError("unexpected ')'".to_string())),
        atom => Ok((Sexpr::Atom(atom.to_string()), pos + 1)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_nested_lists() {
        let src = "(assert (forall ((x U)) (P x)))";
        let parsed = parse_all(src).unwrap();
        assert_eq!(parsed.len(), 1);
        let list = parsed[0].list().unwrap();
        assert_eq!(list[0].atom(), Some("assert"));
    }

    #[test]
    fn ignores_comments() {
        let src = "; a comment\n(check-sat) ; trailing comment";
        let parsed = parse_all(src).unwrap();
        assert_eq!(parsed.len(), 1);
        assert_eq!(parsed[0].list().unwrap()[0].atom(), Some("check-sat"));
    }
}
