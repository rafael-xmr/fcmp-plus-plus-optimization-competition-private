use helioselene_contest::{test_helioselene, bench_helioselene};

fn main() {
    println!("Running tests on the helioselene implementation");
    test_helioselene();
    println!("Tests passed!");

    println!("Running benchmark");
    bench_helioselene();
}

#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub extern "C" fn _start() {
    main();
}
