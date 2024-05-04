use jq_rs::Chunks;

#[test]
fn test_slurp() {
    let mut program = jq_rs::compile(".").unwrap();

    let mut outputs = Vec::new();
    program.run_slurp(Chunks(["123", "45 67", " ", "89 ", "12", " 345"].into_iter().copied().map(str::as_bytes)), |output| outputs.push(output)).unwrap();

    assert_eq!(outputs.len(), 1);

    assert_eq!(serde_json::from_str::<[i32; 5]>(&outputs[0].as_dump_string().unwrap()).unwrap(), [12345, 67, 89, 12, 345]);
}
