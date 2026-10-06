`dictionary.bin` is Brotli's static dictionary, as Google's brotli
repository ships it (`c/common/dictionary.bin`, MIT license, copyright the
Brotli Authors). It is the dictionary of RFC 7932 Appendix A, byte for
byte; `difftest/brotli/dict.py` checks it against the RFC's text and the
CRC-32 the RFC gives.
