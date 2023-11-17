use crate::loc::Location;

#[derive(Debug, Clone)]
pub struct Code {
    pub input: String,
    pub breaks: Vec<isize>,
}

impl Code {
    pub fn new(input: &str) -> Self {
        let breaks: Vec<_> = std::iter::once(-1)
            .chain(
                input
                    .chars()
                    .enumerate()
                    .filter(|(_, c)| *c == '\n')
                    .map(|(i, _)| i as isize),
            )
            .chain(std::iter::once(input.len() as isize))
            .collect();
        Code {
            input: input.to_string(),
            breaks,
        }
    }

    fn report_line(&self, ln: usize, off: isize, res: &mut Vec<String>) {
        let ln = ln as isize + off;
        if ln >= 0 && ln + 1 < self.breaks.len() as isize {
            let ln = ln as usize;
            let l = (self.breaks[ln] + 1) as usize;
            let r = self.breaks[ln + 1] as usize;
            res.push(format!("{:>4}: {}", ln, &self.input[l..r]));
        }
    }

    pub fn mark_location(&self, loc: &Location) -> String {
        let mut res = Vec::new();
        res.push("===".into());
        self.report_line(loc.line, -1, &mut res);
        self.report_line(loc.line, 0, &mut res);
        res.push(format!("      {: <1$}^~~~~", "", loc.column));
        self.report_line(loc.line, 1, &mut res);
        res.push("===".into());
        res.join("\n")
    }

    pub fn get(&self, from: &Location, to: &Location) -> &str {
        &self.input[from.position..to.position]
    }
}
