#[test]
fn test_slurp() {
    let mut program = jq_rs::compile(".").unwrap();
    let result = program.run_slurp(["123", "4567", " ", "890"]).unwrap();
    assert_eq!(result.as_str().trim(), "[1234567,890]");
}
