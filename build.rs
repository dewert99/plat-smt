use std::process::Command;
fn main() {
    // note: add error checking yourself.
    let output = Command::new("git")
        .args(&["describe", "--tags"])
        .output()
        .unwrap();
    let version = String::from_utf8(output.stdout).unwrap();
    println!("cargo:rustc-env=GIT_VERSION={}", version);
}
