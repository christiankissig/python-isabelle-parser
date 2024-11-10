from setuptools import setup, find_packages

extras_require = dict()
extras_require['dev'] = [
    'black',
    'flake8',
    'isort',
]

extras_require['test'] = [
    'pytest',
]

extras_require['ci'] = [
    *extras_require['test'],
    'pytest-cov',
]

setup(
    name="isabelle_parser",
    version="0.0.1",
    description="A parser of Isabelle/Isar artifacts implemented in Python.",
    long_description=open("README.rst").read(),
    long_description_content_type="text/x-rst",
    author="Christian Kissig",
    url="https://github.com/christiankissig/python-isabelle-parser",
    packages=find_packages(),
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',
    install_requires=[
        "ply>=3.0",
    ],
    extras_require=extras_require,
    entry_points={
        'console_scripts': [
            'isaparser = isabelle_parser.cli:main',
            'flake8 = flake8.main.cli:main',
        ],
    },
)
