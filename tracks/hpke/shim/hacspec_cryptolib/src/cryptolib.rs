//! Interface-only stand-in for hacspec_cryptolib, restricted to what hpke-spec calls.
//! Every primitive is opaque to Charon (passed with `--opaque hacspec_cryptolib`).
//! The bodies are never run.
use hacspec_lib::*;

pub type CryptoError = u8;
pub type CryptoByteSeqResult = Result<ByteSeq, CryptoError>;
pub type Key = ByteSeq;
pub type AeadKey = ByteSeq;
pub type AeadIv = ByteSeq;
pub type DhSk = ByteSeq;
pub type DhPk = ByteSeq;

#[derive(Clone, Copy, PartialEq)]
pub enum NamedGroup {
    X25519,
    X448,
    Secp256r1,
    Secp384r1,
    Secp521r1,
}

#[derive(Clone, Copy, PartialEq)]
pub enum HashAlgorithm {
    SHA256,
    SHA384,
    SHA512,
}

#[derive(Clone, Copy, PartialEq)]
pub enum AeadAlgorithm {
    Chacha20Poly1305,
    Aes128Gcm,
    Aes256Gcm,
}

pub fn secret_to_public(_g: &NamedGroup, _x: &DhSk) -> CryptoByteSeqResult {
    unimplemented!()
}
pub fn ecdh(_g: &NamedGroup, _x: &DhSk, _y: &DhPk) -> CryptoByteSeqResult {
    unimplemented!()
}
pub fn valid_private_key(_g: &NamedGroup, _bytes: &DhSk) -> bool {
    unimplemented!()
}
pub fn parse_public_key(_g: &NamedGroup, _bytes: &DhPk) -> Result<DhPk, CryptoError> {
    unimplemented!()
}
pub fn hkdf_extract(_ha: HashAlgorithm, _k: &Key, _salt: &Key) -> CryptoByteSeqResult {
    unimplemented!()
}
pub fn hkdf_expand(_ha: HashAlgorithm, _k: &Key, _info: &ByteSeq, _len: usize) -> CryptoByteSeqResult {
    unimplemented!()
}
pub fn aead_encrypt(_a: &AeadAlgorithm, _k: &AeadKey, _iv: &AeadIv, _msg: &ByteSeq, _aad: &ByteSeq) -> CryptoByteSeqResult {
    unimplemented!()
}
pub fn aead_decrypt(_a: &AeadAlgorithm, _k: &AeadKey, _iv: &AeadIv, _cip: &ByteSeq, _aad: &ByteSeq) -> CryptoByteSeqResult {
    unimplemented!()
}
