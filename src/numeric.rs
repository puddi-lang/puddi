//! Generates the numeric part of the prelude (methods and trait impls for
//! every integer and float type).

use std::fmt::Write as _;

use crate::types::IntTy;

const OPS: [(&str, i32); 3] = [("add", 0), ("sub", 1), ("mul", 2)];

pub fn generate() -> String {
    let mut s = String::new();
    for it in IntTy::all() {
        int_impls(&mut s, it);
    }
    for f in ["Float", "F32"] {
        float_impls(&mut s, f);
    }
    for it in IntTy::all() {
        let n = const_name(it);
        let _ = writeln!(s, "pub const {n}_MIN: {} = {}", it.name(), it.min());
        let _ = writeln!(s, "pub const {n}_MAX: {} = {}", it.name(), it.max());
    }
    s.push_str("pub const INFINITY: Float = 1.0 / 0.0\npub const NAN: Float = 0.0 / 0.0\n");
    s
}

fn const_name(it: IntTy) -> String {
    if it == IntTy::I32 { "INT".into() } else { it.name().to_uppercase() }
}

fn lower(name: &str) -> String {
    name.to_lowercase()
}

fn int_impls(s: &mut String, it: IntTy) {
    let n = it.name();
    let _ = writeln!(s, "impl {n} {{");
    for m in IntTy::all() {
        let mn = m.name();
        let ml = lower(mn);
        let mut conds = Vec::new();
        if m.min() > it.min() {
            conds.push(format!("self >= {}", m.min()));
        }
        if m.max() < it.max() {
            conds.push(format!("self <= {}", m.max()));
        }
        if m == it {
            let _ = writeln!(s, "    pub fn to_{ml}(self) -> Option<{mn}> {{ Some(self) }}");
        } else if conds.is_empty() {
            let _ = writeln!(s, "    pub fn to_{ml}(self) -> Option<{mn}> {{ Some(__cast<{n}, {mn}>(self)) }}");
        } else {
            let _ = writeln!(s, "    pub fn to_{ml}(self) -> Option<{mn}> {{ if {} {{ Some(__cast<{n}, {mn}>(self)) }} else {{ None }} }}", conds.join(" && "));
        }
        let _ = writeln!(s, "    pub fn wrap_to_{ml}(self) -> {mn} {{ __cast<{n}, {mn}>(self) }}");
    }
    if it.bits() <= 32 {
        let _ = writeln!(s, "    pub fn to_float(self) -> Option<Float> {{ Some(__cast<{n}, Float>(self)) }}");
    } else {
        let lo = if it.signed() { "self >= -9007199254740992 && " } else { "" };
        let _ = writeln!(s, "    pub fn to_float(self) -> Option<Float> {{ if {lo}self <= 9007199254740992 {{ Some(__cast<{n}, Float>(self)) }} else {{ None }} }}");
    }
    let _ = writeln!(s, "    pub fn to_f64(self) -> Option<Float> {{ self.to_float() }}");
    if it.bits() <= 16 {
        let _ = writeln!(s, "    pub fn to_f32(self) -> Option<F32> {{ Some(__cast<{n}, F32>(self)) }}");
    } else {
        let lo = if it.signed() { "self >= -16777216 && " } else { "" };
        let _ = writeln!(s, "    pub fn to_f32(self) -> Option<F32> {{ if {lo}self <= 16777216 {{ Some(__cast<{n}, F32>(self)) }} else {{ None }} }}");
    }
    let _ = writeln!(s, "    pub fn round_to_float(self) -> Float {{ __cast<{n}, Float>(self) }}");
    for (o, k) in OPS {
        let _ = writeln!(s, "    pub fn wrapping_{o}(self, other: {n}) -> {n} {{ __wrapping<{n}>({k}, self, other) }}");
        let _ = writeln!(s, "    pub fn checked_{o}(self, other: {n}) -> Option<{n}> {{ if __overflows<{n}>({k}, self, other) {{ None }} else {{ Some(__wrapping<{n}>({k}, self, other)) }} }}");
    }
    let (mn, mx) = (it.min(), it.max());
    let _ = writeln!(s, "    pub fn saturating_add(self, other: {n}) -> {n} {{ if __overflows<{n}>(0, self, other) {{ if other > 0 {{ {mx} }} else {{ {mn} }} }} else {{ self + other }} }}");
    if it.signed() {
        let _ = writeln!(s, "    pub fn saturating_sub(self, other: {n}) -> {n} {{ if __overflows<{n}>(1, self, other) {{ if other < 0 {{ {mx} }} else {{ {mn} }} }} else {{ self - other }} }}");
        let _ = writeln!(s, "    pub fn saturating_mul(self, other: {n}) -> {n} {{ if __overflows<{n}>(2, self, other) {{ if (self < 0) != (other < 0) {{ {mn} }} else {{ {mx} }} }} else {{ self * other }} }}");
        let _ = writeln!(s, "    pub fn checked_div(self, other: {n}) -> Option<{n}> {{ if other == 0 || (self == {mn} && other == -1) {{ None }} else {{ Some(self / other) }} }}");
        let _ = writeln!(s, "    pub fn abs(self) -> {n} {{ if self < 0 {{ 0 - self }} else {{ self }} }}");
        let _ = writeln!(s, "    pub fn signum(self) -> {n} {{ if self < 0 {{ -1 }} else if self > 0 {{ 1 }} else {{ 0 }} }}");
    } else {
        let _ = writeln!(s, "    pub fn saturating_sub(self, other: {n}) -> {n} {{ if other > self {{ 0 }} else {{ self - other }} }}");
        let _ = writeln!(s, "    pub fn saturating_mul(self, other: {n}) -> {n} {{ if __overflows<{n}>(2, self, other) {{ {mx} }} else {{ self * other }} }}");
        let _ = writeln!(s, "    pub fn checked_div(self, other: {n}) -> Option<{n}> {{ if other == 0 {{ None }} else {{ Some(self / other) }} }}");
        let _ = writeln!(s, "    pub fn abs(self) -> {n} {{ self }}");
    }
    let _ = writeln!(s, "    pub fn min(self, other: {n}) -> {n} {{ if other < self {{ other }} else {{ self }} }}");
    let _ = writeln!(s, "    pub fn max(self, other: {n}) -> {n} {{ if other > self {{ other }} else {{ self }} }}");
    let _ = writeln!(s, "    pub fn clamp(self, lo: {n}, hi: {n}) -> {n} {{ if self < lo {{ lo }} else if self > hi {{ hi }} else {{ self }} }}");
    let _ = writeln!(
        s,
        "    pub fn pow(self, exp: Int) -> {n} {{\n        if exp < 0 {{ panic(\"negative exponent\") }}\n        var r: {n} = 1\n        var b = self\n        var e = exp\n        while e > 0 {{\n            if e & 1 == 1 {{ r = r * b }}\n            e = e >> 1\n            if e > 0 {{ b = b * b }}\n        }}\n        r\n    }}"
    );
    let _ = writeln!(s, "    pub fn is_even(self) -> Bool {{ self % 2 == 0 }}");
    let _ = writeln!(s, "    pub fn is_odd(self) -> Bool {{ self % 2 != 0 }}");
    let _ = writeln!(s, "    pub fn to_str(self) -> Str {{ self.show() }}");
    let _ = writeln!(s, "}}");
    let fmt = if it == IntTy::U64 { "__fmt_u64(self)" } else { "__fmt_i64(self)" };
    let _ = writeln!(s, "impl Show for {n} {{ fn show(self) -> Str {{ {fmt} }} }}");
    let _ = writeln!(s, "impl Eq for {n} {{ fn eq(self, other: {n}) -> Bool {{ self == other }} }}");
    let _ = writeln!(s, "impl Ord for {n} {{ fn cmp(self, other: {n}) -> Ordering {{ if self < other {{ Ordering.Less }} else if self > other {{ Ordering.Greater }} else {{ Ordering.Equal }} }} }}");
    let hash = if it.is64() { "(self ^ (self >> 32)).wrap_to_int()" } else if it == IntTy::I32 { "self" } else { "self.wrap_to_int()" };
    let _ = writeln!(s, "impl Hash for {n} {{ fn hash(self) -> Int {{ {hash} }} }}");
    for (t, m, op) in [("Add", "add", "+"), ("Sub", "sub", "-"), ("Mul", "mul", "*"), ("Div", "div", "/"), ("Rem", "rem", "%")] {
        let _ = writeln!(s, "impl {t} for {n} {{ fn {m}(self, other: {n}) -> {n} {{ self {op} other }} }}");
    }
    if it.signed() {
        let _ = writeln!(s, "impl Neg for {n} {{ fn neg(self) -> {n} {{ 0 - self }} }}");
    }
    let _ = writeln!(s, "impl Not for {n} {{ fn not(self) -> {n} {{ !self }} }}");
    let _ = writeln!(s, "impl Transfer for {n} {{ fn __enc(self, b: StrBuilder) {{ __enc_int(b, __cast<{n}, I64>(self)) }} fn __dec(r: __Reader) -> {n} {{ __cast<I64, {n}>(r.i64()) }} }}");
}

fn float_impls(s: &mut String, n: &str) {
    let _ = writeln!(s, "impl {n} {{");
    for (name, k) in [("sqrt", 0), ("floor", 1), ("ceil", 2), ("trunc", 3), ("abs", 5)] {
        let _ = writeln!(s, "    pub fn {name}(self) -> {n} {{ __fop<{n}>({k}, self) }}");
    }
    let _ = writeln!(s, "    pub fn round(self) -> {n} {{ if self >= 0.0 {{ (self + 0.5).floor() }} else {{ (self - 0.5).ceil() }} }}");
    let _ = writeln!(s, "    pub fn round_even(self) -> {n} {{ __fop<{n}>(4, self) }}");
    let _ = writeln!(s, "    pub fn min(self, other: {n}) -> {n} {{ __fminmax<{n}>(0, self, other) }}");
    let _ = writeln!(s, "    pub fn max(self, other: {n}) -> {n} {{ __fminmax<{n}>(1, self, other) }}");
    let _ = writeln!(s, "    pub fn clamp(self, lo: {n}, hi: {n}) -> {n} {{ self.max(lo).min(hi) }}");
    let _ = writeln!(s, "    pub fn is_nan(self) -> Bool {{ self != self }}");
    let _ = writeln!(s, "    pub fn is_finite(self) -> Bool {{ self - self == 0.0 }}");
    let _ = writeln!(s, "    pub fn is_infinite(self) -> Bool {{ !self.is_nan() && !self.is_finite() }}");
    let _ = writeln!(s, "    pub fn signum(self) -> {n} {{ if self > 0.0 {{ 1.0 }} else if self < 0.0 {{ -1.0 }} else {{ self }} }}");
    if n == "Float" {
        let _ = writeln!(s, "    pub fn pow(self, e: Float) -> Float {{ __fmath(0, self, e) }}");
        let _ = writeln!(s, "    pub fn powi(self, e: Int) -> Float {{ __fmath(0, self, __cast<Int, Float>(e)) }}");
        for (name, k) in [("sin", 1), ("cos", 2), ("tan", 3), ("asin", 4), ("acos", 5), ("atan", 6), ("exp", 8), ("ln", 9), ("log2", 10), ("log10", 11), ("cbrt", 12)] {
            let _ = writeln!(s, "    pub fn {name}(self) -> Float {{ __fmath({k}, self, 0.0) }}");
        }
        let _ = writeln!(s, "    pub fn atan2(self, x: Float) -> Float {{ __fmath(7, self, x) }}");
        let _ = writeln!(s, "    pub fn hypot(self, other: Float) -> Float {{ __fmath(13, self, other) }}");
        let _ = writeln!(s, "    pub fn round_to_f32(self) -> F32 {{ __cast<Float, F32>(self) }}");
        let _ = writeln!(s, "    pub fn to_bits(self) -> U64 {{ __reinterpret<Float, U64>(self) }}");
        let _ = writeln!(s, "    pub fn from_bits(b: U64) -> Float {{ __reinterpret<U64, Float>(b) }}");
    } else {
        let _ = writeln!(s, "    pub fn pow(self, e: F32) -> F32 {{ __cast<Float, F32>(__fmath(0, self, e)) }}");
        let _ = writeln!(s, "    pub fn to_float(self) -> Float {{ self }}");
        let _ = writeln!(s, "    pub fn to_bits(self) -> U32 {{ __reinterpret<F32, U32>(self) }}");
        let _ = writeln!(s, "    pub fn from_bits(b: U32) -> F32 {{ __reinterpret<U32, F32>(b) }}");
    }
    for m in IntTy::all() {
        let mn = m.name();
        let ml = lower(mn);
        let _ = writeln!(s, "    pub fn truncate_to_{ml}(self) -> {mn} {{ __cast<{n}, {mn}>(self) }}");
        let _ = writeln!(s, "    pub fn round_to_{ml}(self) -> {mn} {{ __cast<{n}, {mn}>(self.round()) }}");
        let _ = writeln!(
            s,
            "    pub fn to_{ml}(self) -> Option<{mn}> {{ if self.trunc() == self && self >= {}.0 && self < {}.0 {{ Some(__cast<{n}, {mn}>(self)) }} else {{ None }} }}",
            m.min(),
            m.max() + 1
        );
    }
    let _ = writeln!(s, "    pub fn floor_to_int(self) -> Int {{ __cast<{n}, Int>(self.floor()) }}");
    let _ = writeln!(s, "    pub fn ceil_to_int(self) -> Int {{ __cast<{n}, Int>(self.ceil()) }}");
    let _ = writeln!(s, "    pub fn to_str(self) -> Str {{ self.show() }}");
    let _ = writeln!(s, "}}");
    let fmt = if n == "F32" { "__fmt_f32(self)" } else { "__fmt_f64(self)" };
    let _ = writeln!(s, "impl Show for {n} {{ fn show(self) -> Str {{ {fmt} }} }}");
    let _ = writeln!(s, "impl Eq for {n} {{ fn eq(self, other: {n}) -> Bool {{ self == other }} }}");
    let _ = writeln!(s, "impl Ord for {n} {{ fn cmp(self, other: {n}) -> Ordering {{ if self < other {{ Ordering.Less }} else if self > other {{ Ordering.Greater }} else {{ Ordering.Equal }} }} }}");
    let hash = if n == "F32" { "self.to_bits().wrap_to_int()" } else { "let b = self.to_bits()\n (b ^ (b >> 32)).wrap_to_int()" };
    let _ = writeln!(s, "impl Hash for {n} {{ fn hash(self) -> Int {{ {hash} }} }}");
    for (t, m, op) in [("Add", "add", "+"), ("Sub", "sub", "-"), ("Mul", "mul", "*"), ("Div", "div", "/"), ("Rem", "rem", "%")] {
        let _ = writeln!(s, "impl {t} for {n} {{ fn {m}(self, other: {n}) -> {n} {{ self {op} other }} }}");
    }
    let _ = writeln!(s, "impl Neg for {n} {{ fn neg(self) -> {n} {{ -self }} }}");
    let bits = if n == "F32" { "U32" } else { "U64" };
    let _ = writeln!(s, "impl Transfer for {n} {{ fn __enc(self, b: StrBuilder) {{ __enc_int(b, __cast<{bits}, I64>(self.to_bits())) }} fn __dec(r: __Reader) -> {n} {{ {n}.from_bits(__cast<I64, {bits}>(r.i64())) }} }}");
}
