use zuo::Zuo;

fn main() {
    let z = Zuo::builder().init().unwrap();
    let ht = z.make_hash([(c"foo", z.integer(3)), (c"bar", z.integer(4))]);
    println!("=> {}", z.format_write(&ht));
}
