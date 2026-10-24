module

public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on PPC64LE, `sign_message` and `verify_message`: the contracts, evaluated

The preconditions of `signMessageContract` and `verifyMessageContract` by
register (`MSPre`, `MVPre`); and the contracts of the functions on `μ` they
call, `vg_mldsa*_sign` and `vg_mldsa*_verify`: what their preconditions
need (`sign_pre`, `verify_pre`), what their postconditions give
(`sign_post`, `verify_post`), and their public parts (`sign_pub`,
`verify_pub`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Message

open VG VG.PPC64LE
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `sign_message` -/

section
variable (p : Params) (s : State)

/-- `sk`, `msg`, `ctx`, `rnd`, `sig` and `scratch`. -/
abbrev skR : Region := ⟨s.gpr .r3, p.skLen⟩
abbrev msgR : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
abbrev ctxR : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
abbrev rndR : Region := ⟨s.gpr .r8, 32⟩
abbrev sigR : Region := ⟨s.gpr .r9, p.sigLen⟩
abbrev scrR : Region := ⟨s.gpr .r10, messageScratchWords p * 8⟩

end

/-- `signMessageContract`'s precondition, by register. -/
structure MSPre (p : Params) (STK : Nat) (s : State) : Prop where
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
  fk : (s.gpr .r3).toNat + p.skLen ≤ 2 ^ 64
  fm : (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64
  fc : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  fr : (s.gpr .r8).toNat + 32 ≤ 2 ^ 64
  fg : (s.gpr .r9).toNat + p.sigLen ≤ 2 ^ 64
  fx : (s.gpr .r10).toNat + messageScratchWords p * 8 ≤ 2 ^ 64

theorem mspre_of {p : Params} {n : Nat} {s : State}
    (h : (signMessageContract p PPC64LE.abi (n + 1)).pre s) : MSPre p (n + 1) s := by
  sig_pre [signMessageContract, signMessageSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩

/-! ## `verify_message` -/

section
variable (p : Params) (s : State)

/-- `pk`, `sig` and `scratch` (`msg` and `ctx` as signing's). -/
abbrev pkR : Region := ⟨s.gpr .r3, p.pkLen⟩
abbrev vsigR : Region := ⟨s.gpr .r8, p.sigLen⟩
abbrev vscrR : Region := ⟨s.gpr .r9, messageScratchWords p * 8⟩

end

/-- `verifyMessageContract`'s precondition, by register. -/
structure MVPre (p : Params) (STK : Nat) (s : State) : Prop where
  stk : STK ≤ s.sp.toNat
  rd : s.rd = [pkR p s, msgR s, ctxR s, vsigR p s]
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
  fk : (s.gpr .r3).toNat + p.pkLen ≤ 2 ^ 64
  fm : (s.gpr .r4).toNat + (s.gpr .r5).toNat ≤ 2 ^ 64
  fc : (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64
  fg : (s.gpr .r8).toNat + p.sigLen ≤ 2 ^ 64
  fx : (s.gpr .r9).toNat + messageScratchWords p * 8 ≤ 2 ^ 64

theorem mvpre_of {p : Params} {n : Nat} {s : State}
    (h : (verifyMessageContract p PPC64LE.abi (n + 1)).pre s) : MVPre p (n + 1) s := by
  sig_pre [verifyMessageContract, verifyMessageSig, PPC64LE.abi, PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-! ## The functions on `μ` -/

section
variable {p : Params} {stk : Nat} {x y : State}

theorem sign_pre {k m r g c : Addr} (g3 : x.gpr .r3 = k) (g4 : x.gpr .r4 = m) (g5 : x.gpr .r5 = r)
    (g6 : x.gpr .r6 = g) (g7 : x.gpr .r7 = c)
    (hrd : x.rd = [⟨k, p.skLen⟩, ⟨m, 64⟩, ⟨r, 32⟩]) (hwr : x.wr = [⟨g, p.sigLen⟩, ⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat)
    (d1 : Region.Disjoint ⟨k, p.skLen⟩ ⟨g, p.sigLen⟩) (d2 : Region.Disjoint ⟨k, p.skLen⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨m, 64⟩ ⟨g, p.sigLen⟩) (d4 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d5 : Region.Disjoint ⟨r, 32⟩ ⟨g, p.sigLen⟩) (d6 : Region.Disjoint ⟨r, 32⟩ ⟨c, scratchWords p * 8⟩)
    (d7 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, p.skLen⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨r, 32⟩) (b4 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩)
    (b5 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (f1 : k.toNat + p.skLen ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : r.toNat + 32 ≤ 2 ^ 64)
    (f4 : g.toNat + p.sigLen ≤ 2 ^ 64) (f5 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64) :
    (signContract p PPC64LE.abi stk).pre x := by
  sig_pre [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem sign_post (hp : (signContract p PPC64LE.abi stk).post x y) :
    Outcome (fun b => signMu p b (bytesAt x.mem (x.gpr .r3) p.skLen) (bytesAt x.mem (x.gpr .r4) 64)
      (bytesAt x.mem (x.gpr .r5) 32)) ((y.gpr .r3).setWidth 32) (bytesAt y.mem (x.gpr .r6) p.sigLen) := by
  sig_post [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem sign_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6) (h7 : x.gpr .r7 = y.gpr .r7)
    (hl : signLeak p (bytesAt x.mem (x.gpr .r3) p.skLen) (bytesAt x.mem (x.gpr .r4) 64)
        (bytesAt x.mem (x.gpr .r5) 32) =
      signLeak p (bytesAt y.mem (y.gpr .r3) p.skLen) (bytesAt y.mem (y.gpr .r4) 64)
        (bytesAt y.mem (y.gpr .r5) 32)) :
    (signContract p PPC64LE.abi stk).pub x y := by
  sig_pub [signContract, signSig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, hl, h3, h4, h5, h6, h7⟩

theorem verify_pre {k m g c : Addr} (g3 : x.gpr .r3 = k) (g4 : x.gpr .r4 = m) (g5 : x.gpr .r5 = g)
    (g6 : x.gpr .r6 = c)
    (hrd : x.rd = [⟨k, p.pkLen⟩, ⟨m, 64⟩, ⟨g, p.sigLen⟩]) (hwr : x.wr = [⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat)
    (d1 : Region.Disjoint ⟨k, p.pkLen⟩ ⟨c, scratchWords p * 8⟩) (d2 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, p.pkLen⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩) (b4 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (f1 : k.toNat + p.pkLen ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : g.toNat + p.sigLen ≤ 2 ^ 64)
    (f4 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64) :
    (verifyContract p PPC64LE.abi stk).pre x := by
  sig_pre [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs]
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

theorem verify_post (hp : (verifyContract p PPC64LE.abi stk).post x y) :
    let v := fun b => verifyMu p b (bytesAt x.mem (x.gpr .r3) p.pkLen) (bytesAt x.mem (x.gpr .r4) 64)
      (bytesAt x.mem (x.gpr .r5) p.sigLen)
    ((y.gpr .r3).setWidth 32 = 1 ∧ ∃ b, v b = some true) ∨
      ((y.gpr .r3).setWidth 32 = 0 ∧ v minBounds ≠ some true) := by
  sig_post [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs] at hp
  exact hp

theorem verify_pub (hsp : x.sp = y.sp) (h3 : x.gpr .r3 = y.gpr .r3) (h4 : x.gpr .r4 = y.gpr .r4)
    (h5 : x.gpr .r5 = y.gpr .r5) (h6 : x.gpr .r6 = y.gpr .r6)
    (hl : bytesAt x.mem (x.gpr .r3) p.pkLen ++ bytesAt x.mem (x.gpr .r4) 64 ++ bytesAt x.mem (x.gpr .r5) p.sigLen =
      bytesAt y.mem (y.gpr .r3) p.pkLen ++ bytesAt y.mem (y.gpr .r4) 64 ++ bytesAt y.mem (y.gpr .r5) p.sigLen) :
    (verifyContract p PPC64LE.abi stk).pub x y := by
  sig_pub [verifyContract, verifySig, PPC64LE.abi, PPC64LE.argRegs]
  exact ⟨hsp, congrArg leakBytes hl, h3, h4, h5, h6⟩

end

end VG.Proof.MlDsa.PPC64LE.Message
