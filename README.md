# cow_map



A **copy-on-write** map: it starts as a **static lookup table** at compile time (no heap, O(1) lookups) and turns into a normal `HashMap` on first write. Use it when you have a fixed set of defaults but might override a few at runtime.

- **Read-only**: Stays as a static table — zero allocations.
- **First write** (e.g. `insert`, `remove`, `get_mut`): Copies the table into a `HashMap` and then does the write. After that it behaves like a normal `HashMap`.
- **API**: Same as a map: `get`, `insert`, `remove`, `get_mut`, `iter`, `keys`, `values`, `len`, `contains_key`, `to_hashmap`, `into_hashmap`, etc.

## Usage

Add to your `Cargo.toml`:

```toml
[dependencies]
cow_map = "0.1"
phf = { version = "0.13", features = ["macros"] }
```

### Quick start

Use the `cow_map!` macro. You must give the **value type** (keys are `&str` by default):

```rust
use cow_map::cow_map;

fn main() {
    let mut config = cow_map!(i32 =>
        "timeout" => 30,
        "retries" => 3,
        "port"    => 8080,
    );

    // Read-only: no heap, uses the compile-time table
    assert_eq!(config.get("port"), Some(&8080));

    // First write: copies table into a HashMap, then inserts
    config.insert("host", 1);
    assert_eq!(config.get("host"), Some(&1));
    assert_eq!(config.get("port"), Some(&8080));
}
```

### Two ways to use `cow_map!`

**1. Short form** — one map in this block:

```rust
let config = cow_map!(i32 => "timeout" => 30, "port" => 8080);
```

**2. Named form** — when you have **more than one** CowMap in the same scope.

**Why can’t I just use two short forms?** The short form expands to a static variable with a fixed name (`__COW_MAP`). So this:

```rust
let a = cow_map!(i32 => "a" => 1);
let b = cow_map!(i32 => "x" => 10);  // compile error: duplicate `__COW_MAP`
```

would define `static __COW_MAP` twice in the same scope, which Rust doesn’t allow. The named form gives each map its own static name, so they don’t collide:

```rust
let a = cow_map!(A: i32 => "a" => 1);
let b = cow_map!(B: i32 => "x" => 10);  // different static name, OK
```

So: **one map** → short form. **Two or more in the same scope** → named form, with a different name for each (e.g. `DEFAULTS`, `OTHER`).

### Other constructors

- **Key and value types**: `cow_map!(&str, i32 => "timeout" => 30, "port" => 8080)`.
- **From an existing `phf::Map`**: `CowMap::from_static(&my_phf_map)`.
- **From a `HashMap` or owned data**: `CowMap::from(hashmap)`, `CowMap::from([("a", 1), ("b", 2)])`, `.into_iter().collect::<CowMap<_, _>>()`.

## When to use

- **Defaults with optional overrides**: e.g. config that’s fixed at compile time but you might set a few keys at runtime.
- **Lookup tables** that might get extended or modified later.
- **Avoiding heap** when the map is read-only: borrowed mode uses a static table, no `HashMap` until the first write.

## API overview

| Method | Description |
|--------|-------------|
| **`cow_map!(V => k => v, ...)`** | One map in this scope. Value type `V` required (keys are `&str`). |
| **`cow_map!(NAME: V => k => v, ...)`** | Several maps in one scope — give each a unique name so each gets its own static. |
| `from_static(m)` / `borrowed(m)` | Wrap an existing `&'static phf::Map`. |
| `owned_empty()` / `owned(map)` | Start from an empty or existing `HashMap`. |
| `get` / `contains_key` / `len` / `iter` / `keys` / `values` | Read-only; no promotion. |
| `get_mut` / `insert` / `remove` | First use copies the static table into a `HashMap`, then runs the op. |
| `to_hashmap()` | Returns an owned `HashMap` (clone); CowMap unchanged. |
| `into_hashmap(self)` | Consumes the CowMap and returns the `HashMap`. |

**“Promotion”**: The first mutating call (`insert`, `remove`, `get_mut`) copies the compile-time table into a `HashMap` and then does the operation. After that, the CowMap is just a normal `HashMap` under the hood.

## License

Apache-2.0. See [LICENSE](https://github.com/TiernanDeFranco/cow_map/blob/main/LICENSE) in the repo.
