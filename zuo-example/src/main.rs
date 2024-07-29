use zuo::Zuo;

fn main() {
    let z = Zuo::builder().init().unwrap();
    let exp = z.read("(append (list 1 2) (list 3 4))").unwrap();
    let list = z.kernel_eval(&exp);
    for v in z.get_list(&list) {
        println!("=> {}", z.format_print(&v));
    }
}
