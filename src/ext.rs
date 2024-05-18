pub trait Ext {
    fn is_nul_terminated(&self) -> bool;
}

impl Ext for str {
    #[inline]
    fn is_nul_terminated(&self) -> bool {
        self.as_bytes().is_nul_terminated()
    }
}

impl Ext for [u8] {
    #[inline]
    fn is_nul_terminated(&self) -> bool {
        is_nul_terminated(self)
    }
}

/// Returns `true` iff `bytes` is not empty and its last byte is `0`.
pub const fn is_nul_terminated(bytes: &[u8]) -> bool {
    matches!(bytes.last(), Some(0))
}

#[cfg(test)]
mod test {
    use ext::is_nul_terminated;

    #[test]
    fn test_is_nul_terminated() {
        assert!(!is_nul_terminated(&[]));
        assert!(!is_nul_terminated(&[1]));
        assert!(is_nul_terminated(&[1, 0]));
        assert!(!is_nul_terminated(&[0, 1]));
    }
}