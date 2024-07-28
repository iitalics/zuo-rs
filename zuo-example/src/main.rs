fn main() {
    let zuo = zuo::Zuo::init().unwrap();

    let module = zuo.eval_module(
        c"tmp",
        r#"
#lang zuo/kernel
(hash 'answer (~a "Hello" " " "world"))
"#,
    );

    let v = zuo.hash_ref_symbol(&module, c"answer", None).unwrap();
    println!("{}", zuo.format_print(&v));
}
