English | [中文](docs/zh-cn/zh_cn.md)

# pycdc-rapid

A Python bytecode disassembler and decompiler.

Based on Decompyle++ / pycdc:  
https://github.com/zrax/pycdc

Decompyle++ aims to translate compiled Python bytecode back into valid and human-readable Python source code.

Decompyle++ includes two tools:

| Tool | Description |
|---|---|
| `pycdas` | Python bytecode disassembler |
| `pycdc` | Python bytecode decompiler |

## Release

Prebuilt binaries:

https://github.com/Youchuang-Studio/pycdc-rapid/releases

## Building

Generate a project or makefile with CMake, then build the generated project.

Build commands:

```bash
git clone https://github.com/Youchuang-Studio/pycdc-rapid.git
cd pycdc-rapid
mkdir build && cd build
cmake ..
cmake --build . --config Release
```

CMake debug options:

| Option | Description |
|---|---|
| `-DCMAKE_BUILD_TYPE=Debug` | Produce debugging symbols |
| `-DENABLE_BLOCK_DEBUG=ON` | Enable block debugging output |
| `-DENABLE_STACK_DEBUG=ON` | Enable stack debugging output |

Run tests:

```bash
make check JOBS=4
```

Run selected tests only:

```bash
make check JOBS=4 FILTER=xxxx
```

## Usage

Run `pycdas`, the PYC disassembler:

```bash
./pycdas [PATH TO PYC FILE]
```

The bytecode disassembly is printed to `stdout`.

Run `pycdc`, the PYC decompiler:

```bash
./pycdc [PATH TO PYC FILE]
```

The decompiled Python source is printed to `stdout`. Any errors are printed to `stderr`.

## Marshalled code objects

Python marshalled code objects are supported, such as:

```python
marshal.dumps(compile(...))
```

To use this feature, specify the following on the command line:

```bash
-c -v <version>
```

The version must be specified because marshalled code objects do not contain version metadata.

Examples:

```bash
./pycdas -c -v 3.14 example.marshal
./pycdc -c -v 3.14 example.marshal
```

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for issue-report and pull-request requirements.

## Upstream

This project is based on Decompyle++ / pycdc:

https://github.com/zrax/pycdc

## Authors, License and Credits

Decompyle++ is the work of Michael Hansen and Darryl Pogue.

Additional contributions from:

| Contributor |
|---|
| charlietang98 |
| Kunal Parmar |
| Olivier Iffrig |
| Zlodiy |

## License

GNU General Public License v3.0.

See `LICENSE` for details.

## Bilibili

Personal homepage: [Tech悠悠](https://space.bilibili.com/1934537611)

## Sponsor

If this project helps you, donations are appreciated.

![Sponsor QR code](docs/assets/sponsor-qr.jpg)

USDT-TRC20:<br>
[TRKeWXWc1GL7ARE1sX5rBDcYg9yStFsmnU](https://tronscan.org/#/address/TRKeWXWc1GL7ARE1sX5rBDcYg9yStFsmnU)

USDT-Solana:<br>
[BrKPdDdF8NY8k1f4A7RfN1inSDsxZ2d1atDHvGLjp23G](https://solscan.io/account/BrKPdDdF8NY8k1f4A7RfN1inSDsxZ2d1atDHvGLjp23G)
