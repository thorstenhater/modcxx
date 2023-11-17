use modcxx;

#[test]
fn test_scope() {
    let src = r#"
NEURON {
  SUFFIX foobar
}

BREAKPOINT {}

FUNCTION foo(x, y) {
      foo = z*y + x
}"#;

    let raw = modcxx::par::parse(src).expect("No parse");
    let new = modcxx::ast::Module::new(&raw);
    assert!(matches!(new, Err(modcxx::err::ModcxxError::UnboundName(s, _)) if s == "z"));
    let src = r#"
NEURON {
  SUFFIX foobar
  RANGE baz
}

ASSIGNED { baz }

BREAKPOINT {}

PROCEDURE foo(x, y) {
      baz =   z*y + x
}"#;

    let raw = modcxx::par::parse(src).expect("No parse");
    let new = modcxx::ast::Module::new(&raw);
    assert!(matches!(new, Err(modcxx::err::ModcxxError::UnboundName(s, _)) if s == "z"));

    let src = r#"
NEURON {
  SUFFIX foobar
  RANGE baz
}

ASSIGNED { baz }

BREAKPOINT {}

PROCEDURE foo(x, y) {
      LOCAL z
      baz =   z*y + x
}"#;

    let raw = modcxx::par::parse(src).expect("No parse");
    let new = modcxx::ast::Module::new(&raw);
    assert!(new.is_ok());

    let src = r#"
NEURON {
  SUFFIX foobar
  RANGE baz
}

ASSIGNED { baz }

BREAKPOINT {}

PROCEDURE foo(x, y) {
      LOCAL z
      baz =   z*y + x
}"#;

    let raw = modcxx::par::parse(src).expect("No parse");
    let new = modcxx::ast::Module::new(&raw);
    assert!(new.is_ok());
}

#[test]
fn test_access() {
    let src = r#"
NEURON {
  SUFFIX foobar
}

PARAMETER { baz }

BREAKPOINT { baz = 42 }
"#;

    let raw = modcxx::par::parse(src).expect("No parse");
    let new = modcxx::ast::Module::new(&raw);
    assert!(matches!(new, Err(modcxx::err::ModcxxError::WriteToRO(s, _)) if s == "baz"));

    let src = r#"
NEURON {
  SUFFIX foobar
}

PROCEDURE baz() {}

BREAKPOINT { baz = 42 }
"#;

    let raw = modcxx::par::parse(src).expect("No parse");
    let new = modcxx::ast::Module::new(&raw);
    assert!(matches!(new, Err(modcxx::err::ModcxxError::CallableNotVariable(s, _)) if s == "baz"));

    let src = r#"
NEURON {
  SUFFIX foobar
}

PROCEDURE baz() {}

BREAKPOINT { LOCAL baz
baz = 42
baz(23)}
"#;

    let raw = modcxx::par::parse(src).expect("No parse");
    let new = modcxx::ast::Module::new(&raw);
    // TODO Busted as LOCALs are not considered by `use`
    //assert!(matches!(new, Err(modcxx::err::ModcxxError::VariableNotCallable(s, _)) if s == "baz"));

    let src = r#"
NEURON {
  SUFFIX foobar
}

PARAMETER { baz }


BREAKPOINT {
baz(23)}
"#;

    let raw = modcxx::par::parse(src).expect("No parse");
    let new = modcxx::ast::Module::new(&raw);
    assert!(matches!(new, Err(modcxx::err::ModcxxError::VariableNotCallable(s, _)) if s == "baz"));
}
