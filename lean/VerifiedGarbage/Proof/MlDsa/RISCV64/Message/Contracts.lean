module
-- separate module: the contracts' preconditions, built in parallel with `Steps`, which `Sign` also imports

public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on RISC-V, `sign_message` and `verify_message`: the contracts, evaluated

The preconditions of `signMessageContract`, `verifyMessageContract` and
`verifyMessageCachedContract` by register (`MSPre`, `MVPre`, `MVCPre`); and the contracts of the functions on `μ` they
call, `vg_mldsa*_sign` and `vg_mldsa*_verify`: what their preconditions
need (`sign_pre`, `verify_pre`), what their postconditions give
(`sign_post`, `verify_post`), and their public parts (`sign_pub`,
`verify_pub`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `sign_message` -/

section
variable (p : Params) (s : State)

/-- `sk`, `msg`, `ctx`, `rnd`, `sig` and `scratch`. -/
abbrev skR : Region := ⟨s.gpr .a0, p.skLen⟩
abbrev msgR : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
abbrev ctxR : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev rndR : Region := ⟨s.gpr .a5, 32⟩
abbrev sigR : Region := ⟨s.gpr .a6, p.sigLen⟩
abbrev scrR : Region := ⟨s.gpr .a7, messageScratchWords p * 8⟩

end

/-- `signMessageContract`'s precondition, by register. -/
structure MSPre (p : Params) (STK : Nat) (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  stk : STK ≤ s.sp.toNat
  rd : s.rd = [skR p s, msgR s, ctxR s, rndR s]
  wr : s.wr = [sigR p s, scrR p s]
  kg : (skR p s).Disjoint (sigR p s)
  kc : (skR p s).Disjoint (scrR p s)
  mg : (msgR s).Disjoint (sigR p s)
  mc : (msgR s).Disjoint (scrR p s)
  cg : (ctxR s).Disjoint (sigR p s)
  cc : (ctxR s).Disjoint (scrR p s)
  rg : (rndR s).Disjoint (sigR p s)
  rc : (rndR s).Disjoint (scrR p s)
  gc : (sigR p s).Disjoint (scrR p s)
  bk : (below s.sp STK).Disjoint (skR p s)
  bm : (below s.sp STK).Disjoint (msgR s)
  bc : (below s.sp STK).Disjoint (ctxR s)
  br : (below s.sp STK).Disjoint (rndR s)
  bg : (below s.sp STK).Disjoint (sigR p s)
  bx : (below s.sp STK).Disjoint (scrR p s)
  fk : (s.gpr .a0).toNat + p.skLen ≤ 2 ^ 64
  fm : (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64
  fc : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  fr : (s.gpr .a5).toNat + 32 ≤ 2 ^ 64
  fg : (s.gpr .a6).toNat + p.sigLen ≤ 2 ^ 64
  fx : (s.gpr .a7).toNat + messageScratchWords p * 8 ≤ 2 ^ 64
  alx : (s.gpr .a7).toNat % 8 = 0

theorem mspre_of {p : Params} {n : Nat} {s : State}
    (h : (signMessageContract p RISCV64.abi (n + 1)).pre s) : MSPre p (n + 1) s := by
  sig_pre [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25⟩

/-! ## `verify_message` -/

section
variable (p : Params) (s : State)

/-- `pk`, `sig` and `scratch` (`msg` and `ctx` as signing's). -/
abbrev pkR : Region := ⟨s.gpr .a0, p.pkLen⟩
abbrev vsigR : Region := ⟨s.gpr .a5, p.sigLen⟩
abbrev vscrR : Region := ⟨s.gpr .a6, messageScratchWords p * 8⟩

end

/-- `verifyMessageContract`'s precondition, by register, with the further
regions `X` to read (`verifyMessageCachedContract`'s `tr`). -/
structure MVPre (p : Params) (STK : Nat) (X : List Region) (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  stk : STK ≤ s.sp.toNat
  rd : s.rd = [pkR p s, msgR s, ctxR s, vsigR p s] ++ X
  wr : s.wr = [vscrR p s]
  kc : (pkR p s).Disjoint (vscrR p s)
  mc : (msgR s).Disjoint (vscrR p s)
  cc : (ctxR s).Disjoint (vscrR p s)
  gc : (vsigR p s).Disjoint (vscrR p s)
  bk : (below s.sp STK).Disjoint (pkR p s)
  bm : (below s.sp STK).Disjoint (msgR s)
  bc : (below s.sp STK).Disjoint (ctxR s)
  bg : (below s.sp STK).Disjoint (vsigR p s)
  bx : (below s.sp STK).Disjoint (vscrR p s)
  fk : (s.gpr .a0).toNat + p.pkLen ≤ 2 ^ 64
  fm : (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64
  fc : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  fg : (s.gpr .a5).toNat + p.sigLen ≤ 2 ^ 64
  fx : (s.gpr .a6).toNat + messageScratchWords p * 8 ≤ 2 ^ 64
  alx : (s.gpr .a6).toNat % 8 = 0

theorem mvpre_of {p : Params} {n : Nat} {s : State}
    (h : (verifyMessageContract p RISCV64.abi (n + 1)).pre s) : MVPre p (n + 1) [] s := by
  sig_pre [verifyMessageContract, verifyMessageSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

/-! ## `verify_message_cached` -/

/-- `tr`. -/
abbrev trR (s : State) : Region := ⟨s.gpr .a7, 64⟩

/-- `verifyMessageCachedContract`'s precondition, by register: `verify_message`'s, reading `tr` too, which
is `H(pk, 64)`. -/
structure MVCPre (p : Params) (STK : Nat) (s : State) : Prop where
  mv : MVPre p STK [trR s] s
  tc : (vscrR p s).Disjoint (trR s)
  bt : (below s.sp STK).Disjoint (trR s)
  ft : (s.gpr .a7).toNat + 64 ≤ 2 ^ 64
  tr : bytesAt s.mem (s.gpr .a7) 64 = pkTr (bytesAt s.mem (s.gpr .a0) p.pkLen)

theorem mvcpre_of {p : Params} {n : Nat} {s : State}
    (h : (verifyMessageCachedContract p RISCV64.abi (n + 1)).pre s) : MVCPre p (n + 1) s := by
  sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12, h13, h15, h16, h17, h18, h19, h22⟩, h8, h14, h20,
    h21⟩

/-! ## The functions on `μ` -/

section
variable {p : Params} {stk : Nat} {x y : State}

theorem sign_pre {k m r g c : Addr} (g3 : x.gpr .a0 = k) (g4 : x.gpr .a1 = m) (g5 : x.gpr .a2 = r)
    (g6 : x.gpr .a3 = g) (g7 : x.gpr .a4 = c)
    (hrd : x.rd = [⟨k, p.skLen⟩, ⟨m, 64⟩, ⟨r, 32⟩]) (hwr : x.wr = [⟨g, p.sigLen⟩, ⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0) (alc : c.toNat % 8 = 0)
    (d1 : Region.Disjoint ⟨k, p.skLen⟩ ⟨g, p.sigLen⟩) (d2 : Region.Disjoint ⟨k, p.skLen⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨m, 64⟩ ⟨g, p.sigLen⟩) (d4 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d5 : Region.Disjoint ⟨r, 32⟩ ⟨g, p.sigLen⟩) (d6 : Region.Disjoint ⟨r, 32⟩ ⟨c, scratchWords p * 8⟩)
    (d7 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, p.skLen⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨r, 32⟩) (b4 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩)
    (b5 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (f1 : k.toNat + p.skLen ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : r.toNat + 32 ≤ 2 ^ 64)
    (f4 : g.toNat + p.sigLen ≤ 2 ^ 64) (f5 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64) :
    (signContract p RISCV64.abi stk).pre x := by
  sig_pre [signContract, signSig, RISCV64.abi, RISCV64.argRegs]
  simp only [g3, g4, g5, g6, g7]
  and_intros
  -- Only the reserved stack depends on `stk`: split on it in those goals alone.
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem sign_post (hp : (signContract p RISCV64.abi stk).post x y) :
    Outcome (fun b => signMu p b (bytesAt x.mem (x.gpr .a0) p.skLen) (bytesAt x.mem (x.gpr .a1) 64)
      (bytesAt x.mem (x.gpr .a2) 32)) ((y.gpr .a0).setWidth 32) (bytesAt y.mem (x.gpr .a3) p.sigLen) := by
  sig_post [signContract, signSig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem sign_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) (h7 : x.gpr .a4 = y.gpr .a4)
    (hl : signLeak p (bytesAt x.mem (x.gpr .a0) p.skLen) (bytesAt x.mem (x.gpr .a1) 64)
        (bytesAt x.mem (x.gpr .a2) 32) =
      signLeak p (bytesAt y.mem (y.gpr .a0) p.skLen) (bytesAt y.mem (y.gpr .a1) 64)
        (bytesAt y.mem (y.gpr .a2) 32)) :
    (signContract p RISCV64.abi stk).pub x y := by
  sig_pub [signContract, signSig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, hl, h3, h4, h5, h6, h7⟩

theorem verify_pre {k m g c : Addr} (g3 : x.gpr .a0 = k) (g4 : x.gpr .a1 = m) (g5 : x.gpr .a2 = g)
    (g6 : x.gpr .a3 = c)
    (hrd : x.rd = [⟨k, p.pkLen⟩, ⟨m, 64⟩, ⟨g, p.sigLen⟩]) (hwr : x.wr = [⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0) (alc : c.toNat % 8 = 0)
    (d1 : Region.Disjoint ⟨k, p.pkLen⟩ ⟨c, scratchWords p * 8⟩) (d2 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, p.pkLen⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩) (b4 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (f1 : k.toNat + p.pkLen ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : g.toNat + p.sigLen ≤ 2 ^ 64)
    (f4 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64) :
    (verifyContract p RISCV64.abi stk).pre x := by
  sig_pre [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs]
  simp only [g3, g4, g5, g6]
  and_intros
  all_goals first
    | with_reducible assumption
    | (rcases stk with _ | n <;> simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil] <;> and_intros <;> first
        | with_reducible assumption | omega | skip)
    | omega
    | skip
  all_goals assumption

theorem verify_post (hp : (verifyContract p RISCV64.abi stk).post x y) :
    let v := fun b => verifyMu p b (bytesAt x.mem (x.gpr .a0) p.pkLen) (bytesAt x.mem (x.gpr .a1) 64)
      (bytesAt x.mem (x.gpr .a2) p.sigLen)
    ((y.gpr .a0).setWidth 32 = 1 ∧ ∃ b, v b = some true) ∨
      ((y.gpr .a0).setWidth 32 = 0 ∧ v minBounds ≠ some true) := by
  sig_post [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs] at hp
  exact hp

theorem verify_pub (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3)
    (hl : bytesAt x.mem (x.gpr .a0) p.pkLen ++ bytesAt x.mem (x.gpr .a1) 64 ++ bytesAt x.mem (x.gpr .a2) p.sigLen =
      bytesAt y.mem (y.gpr .a0) p.pkLen ++ bytesAt y.mem (y.gpr .a1) 64 ++ bytesAt y.mem (y.gpr .a2) p.sigLen) :
    (verifyContract p RISCV64.abi stk).pub x y := by
  sig_pub [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs]
  exact ⟨hsp, congrArg leakBytes hl, h3, h4, h5, h6⟩

end

end VG.Proof.MlDsa.RISCV64.Message
