// SPDX-FileCopyrightText: 2024 Shun Sakai
//
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Utilities for comparing and ordering values.

#[cfg(test)]
mod tests {
    use super::super::BitU32;

    #[test]
    fn equality() {
        assert_eq!(BitU32::<31>::MIN, BitU32::<31>::MIN);
        assert_ne!(BitU32::<31>::MIN, BitU32::<31>::MAX);
    }

    #[test]
    fn order() {
        assert!(BitU32::<31>::MIN < BitU32::<31>::MAX);
        assert!(BitU32::<31>::MAX > BitU32::<31>::MIN);
    }
}
