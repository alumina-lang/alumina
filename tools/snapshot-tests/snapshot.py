import os
import subprocess
from pathlib import Path

BUILD_DIR = "./build"
COMPILER_PATH = "../../target/debug/alumina-boot"
CORPUS = "../../examples/"

# For examples that accept some stdins
MOCK_STDIN = b"""
Lorem ipsum dolor sit amet, consectetur adipiscing elit. Maecenas quam sapien, tincidunt
id leo et, ultricies sagittis tortor. Aliquam gravida, risus quis posuere posuere, sem
purus pulvinar erat, nec ornare augue erat vel purus. Mauris aliquet libero nisi, id 
faucibus enim ultricies et. Fusce fringilla nisi eu massa tincidunt eleifend. Quisque
leo massa, lobortis non nisi vitae, eleifend dictum felis. Curabitur nulla enim, 
placerat at velit eu, tincidunt fringilla nibh. Sed maximus venenatis eros, hendrerit
blandit sapien pulvinar eu. Donec sit amet nisl quis metus rutrum mattis eu eu massa.
Praesent sit amet ante a mauris sodales interdum vel vitae justo.
""".strip()

def pytest_generate_tests(metafunc):
    if "source_file" in metafunc.fixturenames:
        Path("build").mkdir(parents=True, exist_ok=True)
        for f in os.listdir(BUILD_DIR):
            os.remove(os.path.join(BUILD_DIR, f))

        def get_examples():
            for root, dirs, files in os.walk(CORPUS):
                for name in files:
                    if name.endswith(".alu"):
                        yield (os.path.join(root, name), os.path.join(name))

        test_cases = list(get_examples())


        metafunc.parametrize("source_file", test_cases, ids=[name for _, name in test_cases])


def monkeypatch(filename):
    """Apply patches to generated C code to make the snapshots deterministic"""

    with open(filename, "r") as file:
        filedata = file.read()

    filedata = filedata.replace("getrandom", "getrandom_mock")

    with open(filename, "w") as file:
        file.write(filedata)


def dump(filename, contents):
    """Dump the intermediate results to disk for easier inspection/debugging"""

    with open(os.path.join(BUILD_DIR, filename), "wb") as file:
        file.write(contents)


def test_examples(source_file, snapshot):
    """Testing the API for /me"""

    (example, output) = source_file

    result = subprocess.run(
        [
            COMPILER_PATH,
            "--sysroot",
            "../../stdlib",
            "--output",
            os.path.join(BUILD_DIR, f"{output}.c"),
            f"example={example}",
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )

    compile_ret = result.returncode

    if compile_ret != 0:
        # Some examples may be legit compile errors, we snapshot those too
        dump(f"{output}.compile_stderr", result.stderr)
        
        compile_stderr = result.stderr
        run_ret = None
        run_stdout = None
        run_stderr = None
    else:
        monkeypatch(os.path.join(BUILD_DIR, f"{output}.c"))
        result = subprocess.run(
            [
                "gcc",
                "-O0",
                "-o",
                os.path.join(BUILD_DIR, f"{output}.out"),
                "./monkeypatch.c",
                os.path.join(BUILD_DIR, f"{output}.c"),
            ],
            stderr=subprocess.PIPE,
        )

        # Alumina outputing something that fails to compile is always a bug
        assert result.returncode == 0, f"miscompilation in {source_file}"

        result = subprocess.run(
            [os.path.join(".", f"{output}.out")],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=BUILD_DIR,
            input=MOCK_STDIN
        )

        dump(f"{output}.run_stdout", result.stdout)
        dump(f"{output}.run_stderr", result.stderr)

        compile_stderr = None
        run_ret = result.returncode
        run_stdout = result.stdout
        run_stderr = result.stderr

    snapshot.assert_match(compile_ret, "compile_ret")
    snapshot.assert_match(compile_stderr, "compile_stderr")
    snapshot.assert_match(run_ret, "run_ret")
    snapshot.assert_match(run_stdout, "run_stdout")
    snapshot.assert_match(run_stderr, "run_stderr")
