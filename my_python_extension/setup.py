from setuptools import setup, Extension
from pathlib import Path

# Basic portable flags. You can add -O3 or /O2 here if you like.
extra_compile_args = ["-std=c11", "-Werror"]
workspace_dir = Path.cwd().parent

my_python_ext = Extension(
    name="my_python_ext",                         
    sources=["src/main.c"],
    include_dirs=[workspace_dir / "dist/c/include"],
    define_macros=[],                        # e.g. [("NDEBUG", None)]
    extra_compile_args=extra_compile_args,
    extra_link_args=[workspace_dir / "qiskit/_accelerate.cpython-313-x86_64-linux-gnu.so"]
)

setup(
    name="my_python_ext",
    version="0.1.0",
    ext_modules=[my_python_ext],
)