//! `pud fmt` and `pud doc`.

/// Reformat source text: 4-space indentation by nesting depth, no trailing
/// whitespace, at most one blank line in a row, and a final newline. Only
/// whitespace outside strings and comments changes.
pub fn format(src: &str) -> String {
    let mut out = String::new();
    let mut depth: i32 = 0;
    let mut in_block_comment = 0u32;
    let mut blank_run = 0;
    let mut str_depth = 0u32; // inside a multi-line string literal
    let mut cont = false; // previous line ended with a binary operator
    for raw in src.lines() {
        let line = raw.trim_end();
        let starts_inside = in_block_comment > 0 || str_depth > 0;
        let trimmed = line.trim_start();
        if trimmed.is_empty() && !starts_inside {
            blank_run += 1;
            if blank_run == 1 && !out.is_empty() {
                out.push('\n');
            }
            continue;
        }
        blank_run = 0;
        // count closers at the start of the line to dedent it
        let mut lead_close = 0;
        if !starts_inside {
            for c in trimmed.chars() {
                match c {
                    '}' | ')' | ']' => lead_close += 1,
                    _ => break,
                }
            }
        }
        if lead_close > 0 && out.ends_with("\n\n") {
            out.pop();
        }
        if !starts_inside {
            let extra = if (cont || trimmed.starts_with('.')) && lead_close == 0 { 1 } else { 0 };
            let ind = (depth - lead_close + extra).max(0) as usize;
            out.push_str(&"    ".repeat(ind));
        }
        if !starts_inside {
            let code = strip_line_comment(trimmed);
            cont = ["||", "&&", "+", "-", "*", "/", "%", "=", "->", "|", "&", "^"].iter().any(|op| code.ends_with(op)) && !code.ends_with("//");
        }
        // update depth by scanning the line
        let b = line.as_bytes();
        let mut i = 0;
        while i < b.len() {
            let c = b[i];
            if in_block_comment > 0 {
                if c == b'*' && b.get(i + 1) == Some(&b'/') {
                    in_block_comment -= 1;
                    i += 2;
                    continue;
                }
                if c == b'/' && b.get(i + 1) == Some(&b'*') {
                    in_block_comment += 1;
                    i += 2;
                    continue;
                }
                i += 1;
                continue;
            }
            if str_depth > 0 {
                if c == b'\\' {
                    i += 2;
                    continue;
                }
                if c == b'"' {
                    str_depth = 0;
                }
                i += 1;
                continue;
            }
            match c {
                b'/' if b.get(i + 1) == Some(&b'/') => break,
                b'/' if b.get(i + 1) == Some(&b'*') => {
                    in_block_comment += 1;
                    i += 2;
                    continue;
                }
                b'"' => str_depth = 1,
                b'\'' => {
                    // char literal: skip to closing quote
                    let mut j = i + 1;
                    if b.get(j) == Some(&b'\\') {
                        j += 2;
                    } else {
                        j += 1;
                    }
                    while j < b.len() && b[j] != b'\'' {
                        j += 1;
                    }
                    i = j + 1;
                    continue;
                }
                b'{' | b'(' | b'[' => depth += 1,
                b'}' | b')' | b']' => depth -= 1,
                _ => {}
            }
            i += 1;
        }
        let content = if str_depth > 0 || in_block_comment > 0 { raw } else { line };
        out.push_str(if starts_inside { content } else { content.trim_start() });
        out.push('\n');
    }
    while out.ends_with("\n\n") {
        out.pop();
    }
    if !out.ends_with('\n') {
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    #[test]
    fn format_preserves_multiline_string_spaces() {
        let source = "fn main() {\n    let s = \"first  \nword  \nlast\"\n}\n";
        assert_eq!(super::format(source), source);
    }
}

/// Extract documentation for public items as Markdown.
pub fn doc(module: &str, src: &str) -> Option<String> {
    let mut out = String::new();
    let mut pending: Vec<String> = Vec::new();
    let mut module_doc: Vec<String> = Vec::new();
    let mut depth = 0i32;
    let mut seen_item = false;
    for line in src.lines() {
        let t = line.trim();
        if depth <= 1 {
            if let Some(d) = t.strip_prefix("///") {
                pending.push(d.strip_prefix(' ').unwrap_or(d).to_string());
                continue;
            }
            if !seen_item && depth == 0 {
                if let Some(d) = t.strip_prefix("//") {
                    module_doc.push(d.trim().to_string());
                    continue;
                }
            }
            let is_item = ["pub fn ", "pub struct ", "pub enum ", "pub trait ", "pub type ", "pub const ", "export fn ", "fn ", "struct ", "enum ", "trait ", "impl"]
                .iter()
                .any(|p| t.starts_with(p));
            if is_item {
                seen_item = true;
            }
            let public = t.starts_with("pub ") || t.starts_with("export ");
            if public && (depth == 0 || depth == 1) {
                let sig = t.split(" {").next().unwrap_or(t).trim_end_matches('{').trim();
                let level = if depth == 0 { "###" } else { "####" };
                out.push_str(&format!("{level} `{sig}`\n\n"));
                if !pending.is_empty() {
                    out.push_str(&pending.join("\n"));
                    out.push_str("\n\n");
                }
            } else if depth == 0 && t.starts_with("impl") {
                let sig = t.split(" {").next().unwrap_or(t);
                out.push_str(&format!("### `{sig}`\n\n"));
            }
            if !t.is_empty() && !t.starts_with("@") {
                pending.clear();
            }
        }
        for c in strip_strings(line).chars() {
            match c {
                '{' => depth += 1,
                '}' => depth -= 1,
                _ => {}
            }
        }
    }
    if out.is_empty() && module_doc.is_empty() {
        return None;
    }
    let mut page = format!("## Module `{module}`\n\n");
    let md: Vec<&String> = module_doc.iter().filter(|l| !l.is_empty()).collect();
    if !md.is_empty() {
        page.push_str(&md.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(" "));
        page.push_str("\n\n");
    }
    page.push_str(&out);
    Some(page)
}

fn strip_strings(line: &str) -> String {
    let mut out = String::new();
    let mut in_str = false;
    let mut esc = false;
    let mut chars = line.chars().peekable();
    while let Some(c) = chars.next() {
        if in_str {
            if esc {
                esc = false;
            } else if c == '\\' {
                esc = true;
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        if c == '/' && chars.peek() == Some(&'/') {
            break;
        }
        if c == '"' {
            in_str = true;
            continue;
        }
        if c == '\'' {
            // skip char literal
            let mut n = 0;
            for d in chars.by_ref() {
                n += 1;
                if d == '\'' || n > 10 {
                    break;
                }
            }
            continue;
        }
        out.push(c);
    }
    out
}

fn strip_line_comment(line: &str) -> &str {
    let b = line.as_bytes();
    let mut in_str = false;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'\\' if in_str => i += 1,
            b'"' => in_str = !in_str,
            b'/' if !in_str && b.get(i + 1) == Some(&b'/') => return line[..i].trim_end(),
            _ => {}
        }
        i += 1;
    }
    line
}
