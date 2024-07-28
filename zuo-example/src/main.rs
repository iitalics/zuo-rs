use zuo::Zuo;

fn main() {
    let zuo = Zuo::builder().lib_path("./lib").init().unwrap();

    const MAIN: &str = r#"
#lang zuo
(provide msg)
(define msg (string-join '("hello" "world")))
"#;

    zuo.eval_module(c"main", MAIN);

    let msg = zuo.dynamic_require(c"main", c"msg");
    println!("{}", zuo.format_print(&msg));
}
