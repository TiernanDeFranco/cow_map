//! Example: CowMap — direct init with cow_map!, promotes to HashMap on first write.

use cow_map::cow_map;

fn main() {
    let mut config = cow_map!(CONFIG: i32 =>
        "timeout" => 30,
        "retries" => 3,
        "port"    => 8080,
    );
    println!("Initial state: borrowed = {}", config.is_borrowed());

    // Read-only lookups use the static map
    println!("port   = {:?}", config.get("port"));
    println!("retries = {:?}", config.get("retries"));
    println!("missing = {:?}", config.get("missing"));
    println!("len = {}", config.len());

    // First write: promotes to Owned (copies PHF into a HashMap)
    config.insert("host", 1);
    println!("\nAfter insert: borrowed = {}, owned = {}", config.is_borrowed(), config.is_owned());

    // All original entries are still there; new key added
    println!("port   = {:?}", config.get("port"));
    println!("host   = {:?}", config.get("host"));

    if let Some(v) = config.get_mut("timeout") {
        *v = 60;
    }
    println!("timeout (after mut) = {:?}", config.get("timeout"));

    println!("\nEntries:");
    for (k, v) in config.iter() {
        println!("  {} = {}", k, v);
    }
}
