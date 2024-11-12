// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for comparing and ordering values.

#[cfg(test)]
mod tests {
    use super::super::BitI32;

    #[test]
    fn equality() {
        assert_eq!(BitI32::<31>::MIN, BitI32::<31>::MIN);
        assert_ne!(BitI32::<31>::MIN, BitI32::<31>::MAX);
    }

    #[test]
    fn order() {
        assert!(BitI32::<31>::MIN < BitI32::<31>::MAX);
        assert!(BitI32::<31>::MAX > BitI32::<31>::MIN);
    }
}
