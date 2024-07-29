use zuo::Zuo;

fn main() {
    let z = Zuo::builder().lib_path("./lib").init().unwrap();
    let e = z.read("(+ 1 2)").unwrap();
    let v = z.kernel_eval(&e);
    println!("{}", z.format_print(&v));
}
