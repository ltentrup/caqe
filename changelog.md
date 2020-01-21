# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [4.0.1] - 2020-01-21
### Fixed
- Crash during parsing caused by an empty matrix and innnermost universal quantification (thanks to Andreas Niskanen)
- Crash when requesting partial assignments (`--qdo`) in combination with miniscoping (thanks to Valentin Mayer-Eichberger)
- Fixed rust deprecation warnings and clippy suggestions
