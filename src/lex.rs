use std::iter::Peekable;
use std::str::Chars;

use crate::src::{Code, Location};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Type {
    // General
    Identifier,
    Number,
    Local,
    String,
    Include,
    // Comment
    Comment,
    EndComment,
    Verbatim,
    EndVerbatim,
    Title,
    // Blocks
    Neuron,
    Function,
    Initial,
    Procedure,
    Breakpoint,
    State,
    Parameter,
    Units,
    Assigned,
    Derivative,
    Independent,
    Constant,
    Kinetic,
    Linear,
    NetReceive,
    Destructor,
    // Control flow
    If,
    Else,
    // Kinetic block
    Conserve,
    Tilde,
    LRArrow,
    // Breakpoint block
    Solve,
    Method,
    SteadyState,
    // Process types
    Suffix,
    PointProcess,
    ArtificialCell,
    // Neuron block contents
    Range,
    NonSpecificCurrent,
    Ion,
    Valence,
    Read,
    Write,
    Global,
    Threadsafe,
    Pointer,
    BbcPointer,
    // Operators
    Mul,
    Add,
    Sub,
    Div,
    Pow, // Arithmetic
    Eq,
    NEq,
    LE,
    GE,
    LT,
    GT, // Comparison
    Not,
    Or,
    And,    // Logical
    Assign, // Assignment
    Prime,  // Derivative
    // Pragmas
    UnitsOn,
    UnitsOff,
    // Administrativa
    EOF,
    EOL,
    // Delimiters
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    // Limits
    Table,
    Depend,
    From,
    To,
    Start,
    With,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub typ: Type,
    pub loc: Location,
    pub val: Option<String>, // value, if required; eg Identifiers
}

impl Token {
    fn new(typ: Type, loc: Location) -> Self {
        Token {
            typ,
            loc,
            val: None,
        }
    }

    fn new_with_value(typ: Type, loc: Location, val: &str) -> Self {
        Token {
            typ,
            loc,
            val: Some(val.to_string()),
        }
    }
}

pub const KEYWORDS: [(&'static str, Type); 53] = [
    ("INITIAL", Type::Initial),
    ("DESTRUCTOR", Type::Destructor),
    ("NEURON", Type::Neuron),
    ("INCLUDE", Type::Include),
    ("THREADSAFE", Type::Threadsafe),
    ("POINTER", Type::Pointer),
    ("BBCOREPOINTER", Type::BbcPointer),
    ("SOLVE", Type::Solve),
    ("KINETIC", Type::Kinetic),
    ("LINEAR", Type::Linear),
    ("CONSERVE", Type::Conserve),
    ("METHOD", Type::Method),
    ("STEADYSTATE", Type::SteadyState),
    ("CONSTANT", Type::Constant),
    ("ASSIGNED", Type::Assigned),
    ("Assigned", Type::Assigned),
    ("INDEPENDENT", Type::Independent),
    ("BREAKPOINT", Type::Breakpoint),
    ("UNITS", Type::Units),
    ("UNITSOFF", Type::UnitsOn),
    ("UNITSON", Type::UnitsOff),
    ("STATE", Type::State),
    ("PARAMETER", Type::Parameter),
    ("SUFFIX", Type::Suffix),
    ("POINT_PROCESS", Type::PointProcess),
    ("ARTIFICIAL_CELL", Type::ArtificialCell),
    ("GLOBAL", Type::Global),
    ("RANGE", Type::Range),
    ("TO", Type::To),
    ("FROM", Type::From),
    ("WITH", Type::With),
    ("START", Type::Start),
    ("NONSPECIFIC_CURRENT", Type::NonSpecificCurrent),
    ("USEION", Type::Ion),
    ("WRITE", Type::Write),
    ("VALENCE", Type::Valence),
    ("READ", Type::Read),
    ("FUNCTION", Type::Function),
    ("PROCEDURE", Type::Procedure),
    ("NET_RECEIVE", Type::NetReceive),
    ("DERIVATIVE", Type::Derivative),
    ("LOCAL", Type::Local),
    ("TITLE", Type::Title),
    ("TABLE", Type::Table),
    ("DEPEND", Type::Depend),
    ("COMMENT", Type::Comment),
    ("ENDCOMMENT", Type::EndComment),
    ("VERBATIM", Type::Verbatim),
    ("ENDVERBATIM", Type::EndVerbatim),
    ("IF", Type::If),
    ("if", Type::If),
    ("else", Type::Else),
    ("ELSE", Type::Else),
];

#[derive(Debug, Clone)]
pub struct Lexer {
    pub code: Code,
    pub tokens: Vec<Token>,
    index: usize,
    skip_eol: bool,
}

struct Cursor<'a> {
    code: &'a Code,
    cursor: Peekable<Chars<'a>>,
    location: Location,
}

impl<'a> Cursor<'a> {
    fn new(code: &'a Code) -> Self {
        Self {
            code,
            cursor: code.input.chars().peekable(),
            location: Location::default(),
        }
    }

    /// Advance our state by one char
    fn byte(&mut self) {
        if let Some(c) = self.cursor.next() {
            for _ in 0..c.len_utf8() {
                self.location.byte();
            }
        } else {
            panic!("Past end!");
        }
    }

    /// Single character token
    fn single(&mut self, ty: Type) -> Token {
        let tmp = self.location;
        self.byte();
        Token::new(ty, tmp)
    }

    /// Single *or* two character token, starting w/ the same
    fn or(&mut self, this: Type, c: char, that: Type) -> Token {
        let tok = self.single(this);
        if Some(&c) == self.cursor.peek() {
            self.single(that)
        } else {
            tok
        }
    }

    /// Two character token
    fn and(&mut self, c: char, this: Type) -> Token {
        self.single(this);
        match self.cursor.peek() {
            Some(&d) if d == c => self.single(this),
            Some(&t) => {
                println!(
                    "In line {}: unexpected token {}, wanted {}",
                    self.location.line, t, c
                );
                self.code.mark_location(&self.location);
                panic!();
            }
            None => {
                println!("Unexpected end of file in line {}.", self.location.line);
                panic!();
            }
        }
    }

    fn eol(&mut self) -> Token {
        let tmp = self.location;
        self.cursor.next();
        self.location.line();
        Token::new(Type::EOL, tmp)
    }

    /// Identifier *or* keyword
    fn identifier(&mut self) -> Token {
        use Type::*;
        let beg = self.location;
        while let Some('a'..='z' | 'A'..='Z' | '_' | '0'..='9') = self.cursor.peek() {
            self.byte();
        }
        let code = self.code.get(&beg, &self.location);
        if let Some(p) = KEYWORDS.iter().find(|p| p.0 == code) {
            Token::new(p.1, beg)
        } else {
            Token::new_with_value(Identifier, beg, code)
        }
    }

    /// floating point number: [0-9]+(.[0-9]*)?([eE][+-]?\d+)?
    fn number(&mut self) -> Token {
        let beg = self.location;
        self.integer();
        if self.one_of(".") {
            self.integer();
        }
        if self.one_of("eE") {
            self.one_of("+-");
            self.integer();
        }
        Token::new_with_value(Type::Number, beg, self.code.get(&beg, &self.location))
    }

    fn string(&mut self) -> Token {
        let beg = self.location;
        self.byte(); // Skip "
        loop {
            match self.cursor.peek() {
                Some('\n') => {
                    self.eol();
                }
                Some('"') => {
                    self.byte(); // Skip "
                    break;
                }
                Some('\\') => {
                    // escaped charaters ...
                    self.byte();
                    self.byte();
                }
                Some(_) => {
                    self.byte();
                }
                None => {
                    break;
                }
            }
        }
        Token::new_with_value(Type::String, beg, self.code.get(&beg, &self.location))
    }

    /// integer, only used as part of the float parser
    fn integer(&mut self) -> Token {
        let beg = self.location;
        // TODO(TH): Need at least one char here.
        while let Some('0'..='9') = self.cursor.peek() {
            self.byte();
        }
        Token::new_with_value(Type::Number, beg, self.code.get(&beg, &self.location))
    }

    /// advance by one char, if matches
    fn one_of(&mut self, cs: &str) -> bool {
        match self.cursor.peek() {
            Some(&c) if cs.contains(c) => {
                self.byte();
                true
            }
            _ => false,
        }
    }
}

impl Lexer {
    pub fn new(code: Code) -> Self {
        let mut cursor = Cursor::new(&code);
        let mut tokens = Vec::new();

        use Type::*;
        while let Some(chr) = cursor.cursor.peek() {
            let tok = match chr {
                '.' | '0'..='9' => cursor.number(),
                ' ' | '\t' | '\r' => {
                    cursor.byte();
                    continue;
                }
                ':' | '?' => {
                    loop {
                        match cursor.cursor.peek() {
                            None | Some('\n') => break,
                            Some(_) => cursor.byte(),
                        }
                    }
                    continue;
                }
                '\n' => cursor.eol(),
                '*' => cursor.single(Mul),
                '+' => cursor.single(Add),
                '~' => cursor.single(Tilde),
                '/' => cursor.single(Div),
                '-' => cursor.single(Sub),
                '^' => cursor.single(Pow),
                '\'' => cursor.single(Prime),
                '!' => cursor.or(Not, '=', NEq),
                '=' => cursor.or(Assign, '=', Eq),
                '>' => cursor.or(GT, '=', GE),
                '<' => {
                    let lt = cursor.single(LT);
                    match cursor.cursor.peek() {
                        Some(&'=') => cursor.single(LE),
                        Some(&'-') => {
                            // So ... we might have <-> here ... or x<-42
                            let mut crs = cursor.cursor.clone();
                            crs.next().unwrap();
                            if let Some(&'>') = crs.peek() {
                                cursor.single(Sub);
                                cursor.single(LRArrow)
                            } else {
                                lt
                            }
                        }
                        _ => lt,
                    }
                }
                '{' => cursor.single(LeftBrace),
                '}' => cursor.single(RightBrace),
                '(' => cursor.single(LeftParen),
                ')' => cursor.single(RightParen),
                ',' => cursor.single(Comma),
                '&' => cursor.and('&', And),
                '|' => cursor.and('|', Or),
                '"' => cursor.string(),
                'a'..='z' | 'A'..='Z' | '_' => {
                    let tok = cursor.identifier();
                    while let Some('\t' | ' ') = cursor.cursor.peek() {
                        cursor.byte();
                    }
                    let beg = cursor.location;
                    // Post fix some comment like structures
                    match tok.typ {
                        Title => {
                            loop {
                                match cursor.cursor.peek() {
                                    None | Some('\n') => break,
                                    Some(_) => cursor.byte(),
                                }
                            }
                            Token::new_with_value(
                                Title,
                                beg,
                                cursor.code.get(&beg, &cursor.location),
                            )
                        }
                        Verbatim => {
                            let end = loop {
                                match cursor.cursor.peek() {
                                    None => break cursor.location,
                                    Some('\n') => {
                                        cursor.eol();
                                    }
                                    Some(' ' | '\t' | '\r') => {
                                        cursor.byte();
                                    }
                                    Some(_) => {
                                        let loc = cursor.location;
                                        while let Some(&c) = cursor.cursor.peek() {
                                            if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
                                                break;
                                            }
                                            cursor.byte();
                                        }
                                        let end = cursor.location;
                                        if "ENDVERBATIM" == code.get(&loc, &end) {
                                            break end;
                                        }
                                    }
                                }
                            };
                            Token::new_with_value(Verbatim, beg, cursor.code.get(&beg, &end))
                        }
                        Comment => {
                            let end = loop {
                                match cursor.cursor.peek() {
                                    None => break cursor.location,
                                    Some('\n') => {
                                        cursor.eol();
                                    }
                                    Some(' ' | '\t' | '\r') => {
                                        cursor.byte();
                                    }
                                    Some(_) => {
                                        let loc = cursor.location;
                                        while let Some(&c) = cursor.cursor.peek() {
                                            if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
                                                break;
                                            }
                                            cursor.byte();
                                        }
                                        let end = cursor.location;
                                        if "ENDCOMMENT" == code.get(&loc, &end) {
                                            break loc;
                                        }
                                    }
                                }
                            };
                            Token::new_with_value(Comment, beg, cursor.code.get(&beg, &end))
                        }
                        _ => tok,
                    }
                }
                t => {
                    println!(
                        "Unexpected character: '{}' ({})\n{}",
                        t,
                        t.escape_debug(),
                        code.mark_location(&cursor.location)
                    );
                    panic!();
                }
            };
            tokens.push(tok);
        }
        tokens.push(Token::new(EOF, cursor.location));
        Lexer {
            code,
            tokens,
            index: 0,
            skip_eol: true,
        }
    }

    pub fn advance(&mut self) -> Token {
        let mut idx = self.index;
        while self.tokens[idx].typ == Type::EOL && self.skip_eol {
            idx += 1;
        }
        let tok = self.tokens[idx].clone();
        self.index = idx + 1;
        tok
    }

    /// Return next token, but do not advance our state
    pub fn peek(&self) -> Token {
        let mut idx = self.index;
        while self.tokens[idx].typ == Type::EOL && self.skip_eol {
            idx += 1;
        }
        self.tokens[idx].clone()
    }
}
