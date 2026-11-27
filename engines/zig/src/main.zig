// SPDX-License-Identifier: Apache-2.0
// Copyright (c) 2026 Alexander Stephen Donahue
//
// Spectral Eclipse Frontier -- Zig 0.17.0 Exact Arbitrary-Precision Rational
// Hochstadt Three-Term Orthogonal-Polynomial Reconstructor over Q.
// Built directly on std.math.big.int.Managed with exact GCD normalization
// (ZERO floating-point arithmetic during reconstruction or identity verification!).

const std = @import("std");
const BigInt = std.math.big.int.Managed;

const Rat = struct {
    p: BigInt, // numerator (signed)
    q: BigInt, // denominator (strictly positive, gcd(|p|, q) = 1)
    alloc: std.mem.Allocator,

    fn init(alloc: std.mem.Allocator) !Rat {
        return Rat{
            .p = try BigInt.initSet(alloc, 0),
            .q = try BigInt.initSet(alloc, 1),
            .alloc = alloc,
        };
    }

    fn fromRatio(alloc: std.mem.Allocator, num: i64, den: i64) !Rat {
        std.debug.assert(den != 0);
        var r = try init(alloc);
        if (den < 0) {
            try r.p.set(-num);
            try r.q.set(-den);
        } else {
            try r.p.set(num);
            try r.q.set(den);
        }
        try r.reduce();
        return r;
    }

    fn deinit(self: *Rat) void {
        self.p.deinit();
        self.q.deinit();
    }

    fn copyFrom(self: *Rat, other: *const Rat) !void {
        try self.p.copy(other.p.toConst());
        try self.q.copy(other.q.toConst());
    }

    fn reduce(self: *Rat) !void {
        if (self.p.eqlZero()) {
            try self.q.set(1);
            return;
        }
        if (!self.q.isPositive()) {
            self.p.negate();
            self.q.negate();
        }
        var ap = try self.p.clone();
        defer ap.deinit();
        ap.abs();
        var g = try BigInt.init(self.alloc);
        defer g.deinit();
        try g.gcd(&ap, &self.q);
        var rem = try BigInt.init(self.alloc);
        defer rem.deinit();
        var qn = try BigInt.init(self.alloc);
        defer qn.deinit();
        try qn.divTrunc(&rem, &self.p, &g);
        try self.p.copy(qn.toConst());
        try qn.divTrunc(&rem, &self.q, &g);
        try self.q.copy(qn.toConst());
    }

    fn setAbs(self: *Rat) void {
        self.p.abs();
    }

    fn add(dst: *Rat, a: *const Rat, b: *const Rat) !void {
        var t1 = try BigInt.init(dst.alloc);
        defer t1.deinit();
        var t2 = try BigInt.init(dst.alloc);
        defer t2.deinit();
        try t1.mul(&a.p, &b.q);
        try t2.mul(&b.p, &a.q);
        try dst.p.add(&t1, &t2);
        try dst.q.mul(&a.q, &b.q);
        try dst.reduce();
    }

    fn sub(dst: *Rat, a: *const Rat, b: *const Rat) !void {
        var t1 = try BigInt.init(dst.alloc);
        defer t1.deinit();
        var t2 = try BigInt.init(dst.alloc);
        defer t2.deinit();
        try t1.mul(&a.p, &b.q);
        try t2.mul(&b.p, &a.q);
        try dst.p.sub(&t1, &t2);
        try dst.q.mul(&a.q, &b.q);
        try dst.reduce();
    }

    fn mul(dst: *Rat, a: *const Rat, b: *const Rat) !void {
        var np = try BigInt.init(dst.alloc);
        defer np.deinit();
        var nq = try BigInt.init(dst.alloc);
        defer nq.deinit();
        try np.mul(&a.p, &b.p);
        try nq.mul(&a.q, &b.q);
        try dst.p.copy(np.toConst());
        try dst.q.copy(nq.toConst());
        try dst.reduce();
    }

    fn div(dst: *Rat, a: *const Rat, b: *const Rat) !void {
        std.debug.assert(!b.p.eqlZero());
        var np = try BigInt.init(dst.alloc);
        defer np.deinit();
        var nq = try BigInt.init(dst.alloc);
        defer nq.deinit();
        try np.mul(&a.p, &b.q);
        try nq.mul(&a.q, &b.p);
        try dst.p.copy(np.toConst());
        try dst.q.copy(nq.toConst());
        try dst.reduce();
    }

    fn eql(a: *const Rat, b: *const Rat) bool {
        return a.p.order(b.p) == .eq and a.q.order(b.q) == .eq;
    }

    fn toFloat64(self: *const Rat) f64 {
        const pf: f64 = self.p.toConst().toFloat(f64, .nearest_even)[0];
        const qf: f64 = self.q.toConst().toFloat(f64, .nearest_even)[0];
        return pf / qf;
    }
};

const ReconstructResult = struct {
    a: []Rat,
    b2: []Rat,
    w: []Rat,
};

fn reconstructExactQ(alloc: std.mem.Allocator, lam: []const Rat) !ReconstructResult {
    const n = lam.len;
    var w = try alloc.alloc(Rat, n);
    var sum_u = try Rat.fromRatio(alloc, 0, 1);
    var one = try Rat.fromRatio(alloc, 1, 1);
    var diff = try Rat.init(alloc);
    var prod = try Rat.init(alloc);
    var tmp = try Rat.init(alloc);

    for (0..n) |k| {
        try prod.copyFrom(&one);
        for (0..n) |j| {
            if (j == k) continue;
            try diff.sub(&lam[k], &lam[j]);
            diff.setAbs();
            try tmp.mul(&prod, &diff);
            try prod.copyFrom(&tmp);
        }
        w[k] = try Rat.init(alloc);
        try w[k].div(&one, &prod);
        try tmp.add(&sum_u, &w[k]);
        try sum_u.copyFrom(&tmp);
    }
    for (0..n) |k| {
        try tmp.div(&w[k], &sum_u);
        try w[k].copyFrom(&tmp);
    }

    var a = try alloc.alloc(Rat, n);
    var b2 = try alloc.alloc(Rat, n - 1);
    var p_prev = try alloc.alloc(Rat, n);
    var p_curr = try alloc.alloc(Rat, n);
    var p_next = try alloc.alloc(Rat, n);
    for (0..n) |k| {
        p_prev[k] = try Rat.fromRatio(alloc, 0, 1);
        p_curr[k] = try Rat.fromRatio(alloc, 1, 1);
        p_next[k] = try Rat.fromRatio(alloc, 0, 1);
    }

    var norm_prev = try Rat.fromRatio(alloc, 1, 1);
    var norm_curr = try Rat.init(alloc);
    var num_a = try Rat.init(alloc);
    var term = try Rat.init(alloc);
    var t2 = try Rat.init(alloc);
    var zero = try Rat.fromRatio(alloc, 0, 1);

    for (0..n) |j| {
        try norm_curr.copyFrom(&zero);
        try num_a.copyFrom(&zero);
        for (0..n) |k| {
            try term.mul(&p_curr[k], &p_curr[k]);
            try t2.mul(&w[k], &term);
            try tmp.add(&norm_curr, &t2);
            try norm_curr.copyFrom(&tmp);

            try term.mul(&lam[k], &t2);
            try tmp.add(&num_a, &term);
            try num_a.copyFrom(&tmp);
        }
        a[j] = try Rat.init(alloc);
        try a[j].div(&num_a, &norm_curr);

        if (j > 0) {
            b2[j - 1] = try Rat.init(alloc);
            try b2[j - 1].div(&norm_curr, &norm_prev);
        }
        if (j + 1 == n) break;

        for (0..n) |k| {
            try diff.sub(&lam[k], &a[j]);
            try term.mul(&diff, &p_curr[k]);
            if (j > 0) {
                try t2.mul(&b2[j - 1], &p_prev[k]);
                try p_next[k].sub(&term, &t2);
            } else {
                try p_next[k].copyFrom(&term);
            }
        }
        try norm_prev.copyFrom(&norm_curr);
        for (0..n) |k| {
            try p_prev[k].copyFrom(&p_curr[k]);
            try p_curr[k].copyFrom(&p_next[k]);
        }
    }

    return ReconstructResult{ .a = a, .b2 = b2, .w = w };
}

fn verifyChain(alloc: std.mem.Allocator, label: []const u8, nums: []const i64, den: i64) !void {
    const n = nums.len;
    var lam = try alloc.alloc(Rat, n);
    for (0..n) |k| lam[k] = try Rat.fromRatio(alloc, nums[k], den);

    const res = try reconstructExactQ(alloc, lam);

    // 1. Exact persymmetry over Q!
    for (0..n) |i| {
        if (!Rat.eql(&res.a[i], &res.a[n - 1 - i])) return error.PersymmetryDiagFailed;
    }
    for (0..(n - 1)) |i| {
        if (!Rat.eql(&res.b2[i], &res.b2[n - 2 - i])) return error.PersymmetryOffFailed;
    }

    // 2. Exact trace & Frobenius norm over Q!
    var tr_a = try Rat.fromRatio(alloc, 0, 1);
    var tr_l = try Rat.fromRatio(alloc, 0, 1);
    var frob_j = try Rat.fromRatio(alloc, 0, 1);
    var frob_l = try Rat.fromRatio(alloc, 0, 1);
    var tmp = try Rat.init(alloc);
    var sq = try Rat.init(alloc);
    var two = try Rat.fromRatio(alloc, 2, 1);

    for (0..n) |i| {
        try tmp.add(&tr_a, &res.a[i]);
        try tr_a.copyFrom(&tmp);
        try tmp.add(&tr_l, &lam[i]);
        try tr_l.copyFrom(&tmp);

        try sq.mul(&res.a[i], &res.a[i]);
        try tmp.add(&frob_j, &sq);
        try frob_j.copyFrom(&tmp);

        try sq.mul(&lam[i], &lam[i]);
        try tmp.add(&frob_l, &sq);
        try frob_l.copyFrom(&tmp);
    }
    for (0..(n - 1)) |i| {
        try sq.mul(&two, &res.b2[i]);
        try tmp.add(&frob_j, &sq);
        try frob_j.copyFrom(&tmp);
    }
    if (!Rat.eql(&tr_a, &tr_l)) return error.TraceMismatch;
    if (!Rat.eql(&frob_j, &frob_l)) return error.FrobeniusMismatch;

    // 3. Exact Theorem 10 variance identity over Q: b_0^2 == Var_{e_0}(J)!
    var var_e0 = try Rat.fromRatio(alloc, 0, 1);
    var diff = try Rat.init(alloc);
    for (0..n) |k| {
        try diff.sub(&lam[k], &res.a[0]);
        try sq.mul(&diff, &diff);
        try tmp.mul(&res.w[k], &sq);
        try diff.add(&var_e0, &tmp);
        try var_e0.copyFrom(&diff);
    }
    if (!Rat.eql(&res.b2[0], &var_e0)) return error.VarianceIdentityFailed;

    std.debug.print("[Zig-Q] {s:<22} N={d:2} exact_Q persym=OK trace=OK frob=OK b0^2=Var_e0={d:.6} (a0={d:.4})\n", .{ label, n, res.b2[0].toFloat64(), res.a[0].toFloat64() });
}

fn verifyTheorem9J14(alloc: std.mem.Allocator) !void {
    const spec = [_]i64{ 0, 1, 4, 9, 10 };
    var lam: [5]Rat = undefined;
    for (0..5) |k| lam[k] = try Rat.fromRatio(alloc, spec[k], 1);
    const res = try reconstructExactQ(alloc, &lam);

    const exp_a = [_]i64{ 4, 6, 4, 6, 4 };
    const exp_b2_n = [_]i64{ 15, 9, 9, 15 };
    const exp_b2_d = [_]i64{ 1, 2, 2, 1 };

    for (0..5) |i| {
        const ea = try Rat.fromRatio(alloc, exp_a[i], 1);
        if (!Rat.eql(&res.a[i], &ea)) return error.J14DiagMismatch;
    }
    for (0..4) |i| {
        const eb = try Rat.fromRatio(alloc, exp_b2_n[i], exp_b2_d[i]);
        if (!Rat.eql(&res.b2[i], &eb)) return error.J14OffDiagMismatch;
    }
    std.debug.print("[Zig-Q] Theorem 9 J_{{1,4}} {{0,1,4,9,10}} EXACT over Q: a=(4,6,4,6,4), b^2=(15, 9/2, 9/2, 15) VERIFIED!\n", .{});
}

pub fn main() !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const alloc = arena.allocator();

    std.debug.print("[Zig-Q] Spectral Eclipse Exact Arbitrary-Precision Rational Hochstadt Engine (Zig 0.17.0)\n", .{});

    try verifyChain(alloc, "4x4_noESE_1_3", &.{ -3, -1, 1, 3 }, 2);
    try verifyChain(alloc, "5x5_ESE_3_4", &.{ -4, -3, 0, 3, 4 }, 1);
    try verifyChain(alloc, "6x6_noESE_1_3_5", &.{ -5, -3, -1, 1, 3, 5 }, 2);
    try verifyChain(alloc, "7x7_noESE_1_2_3", &.{ -3, -2, -1, 0, 1, 2, 3 }, 1);
    try verifyChain(alloc, "7x7_ESE_3_4_5", &.{ -5, -4, -3, 0, 3, 4, 5 }, 1);
    try verifyChain(alloc, "8x8_rupture_m1", &.{ -11, -9, -7, -1, 1, 7, 9, 11 }, 2);
    try verifyChain(alloc, "9x9_critical_1234", &.{ -4, -3, -2, -1, 0, 1, 2, 3, 4 }, 1);
    try verifyChain(alloc, "11x11_subcrit_m5", &.{ -13, -12, -11, -10, -1, 0, 1, 10, 11, 12, 13 }, 1);
    try verifyChain(alloc, "11x11_supercrit_m6", &.{ -15, -14, -13, -12, -1, 0, 1, 12, 13, 14, 15 }, 1);
    try verifyTheorem9J14(alloc);

    std.debug.print("[Zig-Q] ALL 10 EXACT RATIONAL RECONSTRUCTIONS & THEOREM 9/10 IDENTITIES PASSED.\n", .{});
}
