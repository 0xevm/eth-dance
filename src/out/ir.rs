use crate::typing::Typing;

pub fn to_ir(typing: &Typing) -> Vec<String> {
  let mut v = Vec::new();
  for (id, info) in &typing.infos {
    let abi_str = match info.expr.returns.abi() {
      Some(ty) => format!(": {}", ty),
      None => String::new(),
    };
    let mut s = format!("{}{} = {}", id, abi_str, info.expr.code);
    if !info.display.starts_with("$$") {
      let comment = format!("# {}: {}", info.display, info.ty());
      s = format!("{}\n{}", comment, s);
    }
    v.push(s);
  }
  v
}
