# cow_map

A copy-on-write map: static lookup at compile time (no heap), turns into a `HashMap` on first write.

```toml
[dependencies]
cow_map = "0.1"
```

The macro **requires a name** for the static PHF:

```rust
use cow_map::cow_map;

let mut config = cow_map!(CONFIG: i32 =>
    "timeout" => 30,
    "retries" => 3,
    "port"    => 8080,
);
assert_eq!(config.get("port"), Some(&8080));
config.insert("host", 1);
assert_eq!(config.get("host"), Some(&1));
```

With key+value types: `cow_map!(NAME: &str, i32 => "k" => 1, ...)`. Other: `CowMap::from_static(&phf_map)`; `CowMap::from(hashmap)`; `to_hashmap()`, `into_hashmap()`.

## License

Apache-2.0. [LICENSE](https://github.com/TiernanDeFranco/cow_map/blob/main/LICENSE)
