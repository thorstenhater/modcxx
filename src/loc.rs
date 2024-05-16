#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord)]
pub struct Location {
    pub line: usize,     // line number
    pub column: usize,   // column number
    pub position: usize, // position in characters
}

impl Location {
    pub fn new(line: usize, column: usize, position: usize) -> Self {
        Location {
            line,
            column,
            position,
        }
    }

    pub fn byte(&mut self) {
        self.position += 1;
        self.column += 1;
    }

    pub fn line(&mut self) {
        self.position += 1;
        self.column = 0;
        self.line += 1;
    }
}
