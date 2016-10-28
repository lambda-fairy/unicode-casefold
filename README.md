# unicode-casefold

Iterators for case folding text. Provides "simple" and "full" algorithms, with Turkic language options on both.

See [this W3C article][1] for how case folding differs from `.to_lowercase()`.

[1]: https://www.w3.org/International/wiki/Case_folding


## Updating the Unicode data tables

The tables used by this library are generated from official Unicode Consortium data. To update them, run the following commands:

```sh
curl -O http://www.unicode.org/Public/UNIDATA/CaseFolding.txt
python3 scripts/generate.py < CaseFolding.txt > src/tables.rs
rm CaseFolding.txt
```

Then check in any changes.
