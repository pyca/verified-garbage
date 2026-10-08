import VerifiedGarbage.Proof.Ecdh.X86_64.Window

/-!
# ECDH on x86-64: what the whole function needs of its scalar multiplication

`Cfg.exchangeWith c mq` is the exchange with any program `mq` computing
`[d]P` into `R`, followed by the signature's power `Z^(p-2)`. `MulOk c mq W`
says that `mq` and the power do so, writing only the areas `W` of the working
space (`MulPostW`), from what the exchange has established before it: the
signature's constants (`Fixed`), `b R` in `BP`, the point `P` (the peer's, or
`G`) at `PX`, `PY`, `ONEP`, `R` the point at infinity, `d` at `K` and its
bits in the first table, and those of `p - 2` in the second. `MulW c W` is
what the rest of the exchange needs of `W`: it keeps the constants
(`FixedOk`), `d` (`D`) and the flag.

`mulQ_ok` and `mulQ_w`: the window method (or the ladder), `mulPow_ok`.
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-- What a scalar multiplication and the power leave, writing only `W`: `R`
represents `[k]P` for `k` in `[1, n-1]`, and `ACC` holds `Z^(p-2)`. -/
structure MulPostW (c : Cfg) (W : List (Nat × Nat)) (base : Addr) (P : Point c.C) (k : Nat)
    (s s' : State) : Prop where
  scr : Scr s' base size
  rsi : s'.gpr .rsi = s.gpr .rsi
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base W s.mem s'.mem
  q : 1 ≤ k → k < c.C.n → Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s' RZ < c.C.p

/-- `mq`, then the power, computes `[k]P` and `Z^(p-2)` (`MulPostW`), writing only
`W`, from the state the exchange leaves before it. -/
def MulOk (c : Cfg) (mq : Prog isa) (W : List (Nat × Nat)) : Prop :=
  ∀ {base : Addr} {s : State}, Scr s base size →
    ∀ {g : Reg → BitVec 64}, Fixed c base g s.mem → sv c base s BP = c.mont c.C.b →
    ∀ {P : Point c.C}, onCurve c.C P = true → sv c base s PX < c.C.p → sv c base s PY < c.C.p →
    Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P →
    sv c base s RX = 0 → sv c base s RY = c.mont 1 → sv c base s RZ = 0 →
    ∀ {k : Nat}, sv c base s K = k → k < 2 ^ (8 * c.C.len) →
    (∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0) →
    (∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0) →
    ∀ {rest : Prog isa} {R : State → Prop}, (∀ s', MulPostW c W base P k s s' → WP isa rest s' R) →
    WP isa (.seq mq (.seq c.pPow rest)) s R

/-- What the exchange needs of the areas `W` the multiplication writes: they
keep the constants, `d` and the flag. -/
structure MulW (c : Cfg) (W : List (Nat × Nat)) : Prop where
  fixed : FixedOk c W
  d : ∀ w ∈ W, c.sl D + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl D
  flag : ∀ w ∈ W, c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG

/-- What `mulQ` (the window method or the ladder) and the power may write. -/
abbrev mulQW (c : Cfg) : List (Nat × Nat) := winX c ++ slW c mulI ++ pwW c

theorem mulQ_ok (hc : BaseCfgOk c) (hC : Law c.C) : MulOk c (Impl.Ecdh.X86_64.Cfg.mulQ c) (mulQW c) :=
  fun hs _ F hbp _ hP hpx hpy hrep hrx hry hrz _ hk hk8 ht₀ ht₁ _ _ h =>
    mulPow_ok hc hC hs F hbp hP hpx hpy hrep hrx hry hrz hk hk8 ht₀ ht₁ fun s' L =>
      h s' ⟨L.scr, L.gpr _ (rsi_not_invClob _), L.rd, L.wr, L.unch,
        fun _ hn => L.q (Nat.lt_of_lt_of_le hn hc.n_bits), L.acc_lt, L.acc, L.rz_lt⟩

theorem mulQ_w (hc : BaseCfgOk c) : MulW c (mulQW c) where
  fixed := fixedOk_mulW
  d := apart_mulW (by decide) (by decide) (by decide)
  flag := fun w hw => by
    have := hc.n0
    rcases apart_mulW (c := c) (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h

end VG.Proof.Ecdh.X86_64
