use crate::typing::Typing;

pub fn to_ir(typing: &Typing) -> Vec<String> {
  let mut v = Vec::new();
  for (id, info) in &typing.infos {
    let mut s = format!("{}: {} = {}", id, info.ty(), info.expr.code);
    if !info.display.starts_with("$$") {
      s = format!("# {}\n{}", info.display, s);
    }
    v.push(s);
  }
  v
}
