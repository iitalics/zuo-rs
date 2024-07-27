use std::env;
use std::path::PathBuf;

fn main() {
    let zuo_path = env::var_os("ZUO_SOURCE")
        .map(PathBuf::from)
        .unwrap_or_else(|| env::current_dir().unwrap());

    let zuo_c = zuo_path.join("zuo.c");
    if !zuo_c.is_file() {
        panic!("zuo.c not found");
    }

    cc::Build::new()
        .file(zuo_c)
        .define("ZUO_EMBEDDED", "1")
        .opt_level(2)
        .warnings(false)
        .cargo_metadata(true)
        .compile("zuo")
}
