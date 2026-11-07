module
-- separate module: the contracts' preconditions, built in parallel with `Steps`, which `Sign` also imports

public import VerifiedGarbage.Spec.MlDsa.Contract
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on RISC-V, `sign_message` and `verify_message_cached`: the contracts, evaluated

The preconditions of `signMessageContract` and `verifyMessageCachedContract`
by register (`MSPre`, `MVCPre`, of which `MVPre` is most); and the contracts of the functions on `μ` they
call, `vg_mldsa*_sign` and `vg_mldsa*_verify`: what their preconditions
need (`sign_pre`, `verify_pre`), what their postconditions give
(`sign_post`, `verify_post`), and their public parts (`sign_pub`,
`verify_pub`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PreparedKey

open VG VG.RISCV64 VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The length of the key a signing function is given: encoded, or prepared (`q`). -/
def skBytes : Bool → Nat
  | true => preparedSecretKeyBytes p
  | false => p.skLen

/-- The contract of a signing function on `μ`, with an encoded or a prepared (`q`) key. -/
def signEK (q : Bool) (stk : Nat) : Contract isa :=
  if q then preparedSignContract p RISCV64.abi stk else signContract p RISCV64.abi stk

/-- The length of the key a verification function is given. -/
def pkBytes : Bool → Nat
  | true => preparedPublicKeyBytes p
  | false => p.pkLen

/-- The contract of a verification function on `μ`, with an encoded or a prepared (`q`) key. -/
def verifyEK (q : Bool) (stk : Nat) : Contract isa :=
  if q then preparedVerifyContract p RISCV64.abi stk else verifyContract p RISCV64.abi stk

end

/-- Memories that agree on the `kl + 1024 N` bytes at `key` hold the same polynomials after `kl`. -/
theorem polys_congr {m₁ m₂ : Mem} {key : Addr} {kl N : Nat}
    (hs : ∀ k < kl + 1024 * N, m₂ (key + BitVec.ofNat 64 k) = m₁ (key + BitVec.ofNat 64 k)) {F : Nat → Poly}
    (h : ∀ i < N, Proof.MlDsa.PolyIs m₁ (key + BitVec.ofNat 64 (kl + 4 * VG.Spec.MlDsa.n * i)) (F i)) :
    ∀ i < N, Proof.MlDsa.PolyIs m₂ (key + BitVec.ofNat 64 (kl + 4 * VG.Spec.MlDsa.n * i)) (F i) := fun i hi => by
  have hc : ∀ k < 1024, m₂ (key + BitVec.ofNat 64 (kl + 4 * VG.Spec.MlDsa.n * i) + BitVec.ofNat 64 k) =
      m₁ (key + BitVec.ofNat 64 (kl + 4 * VG.Spec.MlDsa.n * i) + BitVec.ofNat 64 k) := fun k hk => by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hs _ (by simp only [VG.Spec.MlDsa.n]; omega)
  refine ⟨fun j hj => by rw [Proof.MlDsa.Arith.coeffAt_congr hc hj]; exact (h i hi).1 j hj, ?_⟩
  rw [← (h i hi).2]
  unfold Proof.MlDsa.polyAt
  congr 1
  funext j
  rw [Proof.MlDsa.Arith.coeffAt_congr hc j.isLt]

/-- A prepared private key, in memory whose bytes of it are the same. -/
theorem preparedSecret_of_bytes {p : Params} {m m' : Mem} {key : Addr}
    (h : bytesAt m' key (preparedSecretKeyBytes p) = bytesAt m key (preparedSecretKeyBytes p))
    (hk : PreparedSecretKey p m key) : PreparedSecretKey p m' key := by
  have hs : ∀ k < preparedSecretKeyBytes p, m' (key + BitVec.ofNat 64 k) = m (key + BitVec.ofNat 64 k) :=
    fun k hk => by
      have := congrArg (fun xs : List Byte => xs.getD k 0) h
      rwa [Proof.MlKem.bytesAt_getD _ _ hk, Proof.MlKem.bytesAt_getD _ _ hk] at this
  have hl : p.skLen ≤ preparedSecretKeyBytes p := by unfold preparedSecretKeyBytes; omega
  rw [Proof.MlDsa.preparedSecretKey_iff] at hk ⊢
  rw [Proof.MlKem.bytesAt_congr (m := m) (m' := m') fun i hi => hs i (by omega)]
  exact polys_congr (kl := p.skLen) (N := p.ℓ + 2 * p.k) (fun k hk => hs k (by
    unfold preparedSecretKeyBytes; simp only [VG.Spec.MlDsa.n] at hk ⊢; omega)) hk

/-- A prepared public key, in memory whose bytes of it are the same. -/
theorem preparedPublic_of_bytes {p : Params} {m m' : Mem} {key : Addr}
    (h : bytesAt m' key (preparedPublicKeyBytes p) = bytesAt m key (preparedPublicKeyBytes p))
    (hk : PreparedPublicKey p m key) : PreparedPublicKey p m' key := by
  have hs : ∀ k < preparedPublicKeyBytes p, m' (key + BitVec.ofNat 64 k) = m (key + BitVec.ofNat 64 k) :=
    fun k hk => by
      have := congrArg (fun xs : List Byte => xs.getD k 0) h
      rwa [Proof.MlKem.bytesAt_getD _ _ hk, Proof.MlKem.bytesAt_getD _ _ hk] at this
  have hl : p.pkLen ≤ preparedPublicKeyBytes p := by unfold preparedPublicKeyBytes; omega
  rw [Proof.MlDsa.preparedPublicKey_iff] at hk ⊢
  rw [Proof.MlKem.bytesAt_congr (m := m) (m' := m') fun i hi => hs i (by omega)]
  exact polys_congr (kl := p.pkLen) (N := p.k) (fun k hk => hs k (by
    unfold preparedPublicKeyBytes; simp only [VG.Spec.MlDsa.n] at hk ⊢; omega)) hk

end VG.Proof.MlDsa.RISCV64.PreparedKey

namespace VG.Proof.MlDsa.RISCV64.Message

open VG VG.RISCV64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `sign_message` -/

section
variable (p : Params) (s : State)

/-- `sk` (encoded, or prepared: `q`), `msg`, `ctx`, `rnd`, `sig` and `scratch`. -/
abbrev skR (q : Bool) : Region := ⟨s.gpr .a0, PreparedKey.skBytes p q⟩
abbrev msgR : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
abbrev ctxR : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev rndR : Region := ⟨s.gpr .a5, 32⟩
abbrev sigR : Region := ⟨s.gpr .a6, p.sigLen⟩
abbrev scrR : Region := ⟨s.gpr .a7, messageScratchWords p * 8⟩

end

/-- `sign_message`'s contract, with an encoded or a prepared (`q`) key. -/
def signMessageEK (p : Params) (q : Bool) (stk : Nat) : Contract isa :=
  if q then preparedSignMessageContract p RISCV64.abi stk else signMessageContract p RISCV64.abi stk

/-- `signMessageEK`'s precondition, by register. -/
structure MSPre (p : Params) (q : Bool) (STK : Nat) (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  stk : STK ≤ s.sp.toNat
  rd : s.rd = [skR p s q, msgR s, ctxR s, rndR s]
  wr : s.wr = [sigR p s, scrR p s]
  kg : (skR p s q).Disjoint (sigR p s)
  kc : (skR p s q).Disjoint (scrR p s)
  mg : (msgR s).Disjoint (sigR p s)
  mc : (msgR s).Disjoint (scrR p s)
  cg : (ctxR s).Disjoint (sigR p s)
  cc : (ctxR s).Disjoint (scrR p s)
  rg : (rndR s).Disjoint (sigR p s)
  rc : (rndR s).Disjoint (scrR p s)
  gc : (sigR p s).Disjoint (scrR p s)
  bk : (below s.sp STK).Disjoint (skR p s q)
  bm : (below s.sp STK).Disjoint (msgR s)
  bc : (below s.sp STK).Disjoint (ctxR s)
  br : (below s.sp STK).Disjoint (rndR s)
  bg : (below s.sp STK).Disjoint (sigR p s)
  bx : (below s.sp STK).Disjoint (scrR p s)
  fk : (s.gpr .a0).toNat + PreparedKey.skBytes p q ≤ 2 ^ 64
  fm : (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64
  fc : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  fr : (s.gpr .a5).toNat + 32 ≤ 2 ^ 64
  fg : (s.gpr .a6).toNat + p.sigLen ≤ 2 ^ 64
  fx : (s.gpr .a7).toNat + messageScratchWords p * 8 ≤ 2 ^ 64
  alx : (s.gpr .a7).toNat % 8 = 0
  kp : q = true → PreparedSecretKey p s.mem (s.gpr .a0)

theorem mspre_of {p : Params} {q : Bool} {n : Nat} {s : State}
    (h : (signMessageEK p q (n + 1)).pre s) : MSPre p q (n + 1) s := by
  cases q
  · simp only [signMessageEK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pre [signMessageContract, signMessageSig, RISCV64.abi, RISCV64.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24, h25⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24, h25, fun h => absurd h (by decide)⟩
  · simp only [signMessageEK, ↓reduceIte] at h
    sig_pre [preparedSignMessageContract, preparedSignMessageSig, RISCV64.abi, RISCV64.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24, h25, h26⟩ := h
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23, h24, h26, fun _ => h25⟩

/-! ## `verify_message_cached` -/

section
variable (p : Params) (s : State)

/-- `pk` (encoded, or prepared: `q`), `sig` and `scratch` (`msg` and `ctx` as signing's). -/
abbrev pkR (q : Bool) : Region := ⟨s.gpr .a0, PreparedKey.pkBytes p q⟩
abbrev vsigR : Region := ⟨s.gpr .a5, p.sigLen⟩
abbrev vscrR : Region := ⟨s.gpr .a6, messageScratchWords p * 8⟩

end

/-- Most of `verifyMessageCachedContract`'s precondition, by register, with
the further regions `X` to read (its `tr`). -/
structure MVPre (p : Params) (q : Bool) (STK : Nat) (X : List Region) (s : State) : Prop where
  al : s.sp.toNat % 16 = 0
  stk : STK ≤ s.sp.toNat
  rd : s.rd = [pkR p s q, msgR s, ctxR s, vsigR p s] ++ X
  wr : s.wr = [vscrR p s]
  kc : (pkR p s q).Disjoint (vscrR p s)
  mc : (msgR s).Disjoint (vscrR p s)
  cc : (ctxR s).Disjoint (vscrR p s)
  gc : (vsigR p s).Disjoint (vscrR p s)
  bk : (below s.sp STK).Disjoint (pkR p s q)
  bm : (below s.sp STK).Disjoint (msgR s)
  bc : (below s.sp STK).Disjoint (ctxR s)
  bg : (below s.sp STK).Disjoint (vsigR p s)
  bx : (below s.sp STK).Disjoint (vscrR p s)
  fk : (s.gpr .a0).toNat + PreparedKey.pkBytes p q ≤ 2 ^ 64
  fm : (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64
  fc : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  fg : (s.gpr .a5).toNat + p.sigLen ≤ 2 ^ 64
  fx : (s.gpr .a6).toNat + messageScratchWords p * 8 ≤ 2 ^ 64
  alx : (s.gpr .a6).toNat % 8 = 0

/-- `tr`. -/
abbrev trR (s : State) : Region := ⟨s.gpr .a7, 64⟩

/-- `verifyMessageCachedContract`'s precondition, by register: `MVPre`, reading `tr` too, which is
`H(pk, 64)`. -/
structure MVCPre (p : Params) (q : Bool) (STK : Nat) (s : State) : Prop where
  mv : MVPre p q STK [trR s] s
  tc : (vscrR p s).Disjoint (trR s)
  bt : (below s.sp STK).Disjoint (trR s)
  ft : (s.gpr .a7).toNat + 64 ≤ 2 ^ 64
  tr : bytesAt s.mem (s.gpr .a7) 64 = pkTr (bytesAt s.mem (s.gpr .a0) p.pkLen)
  kp : q = true → PreparedPublicKey p s.mem (s.gpr .a0)

/-- `verify_message_cached`'s contract, with an encoded or a prepared (`q`) key. -/
def verifyMessageEK (p : Params) (q : Bool) (stk : Nat) : Contract isa :=
  if q then preparedVerifyMessageContract p RISCV64.abi stk else verifyMessageCachedContract p RISCV64.abi stk

theorem mvcpre_of {p : Params} {q : Bool} {n : Nat} {s : State}
    (h : (verifyMessageEK p q (n + 1)).pre s) : MVCPre p q (n + 1) s := by
  cases q
  · simp only [verifyMessageEK, Bool.false_eq_true, ↓reduceIte] at h
    sig_pre [verifyMessageCachedContract, verifyMessageCachedSig, RISCV64.abi, RISCV64.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22⟩ := h
    exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12, h13, h15, h16, h17, h18, h19, h22⟩, h8, h14, h20,
      h21, fun h => absurd h (by decide)⟩
  · simp only [verifyMessageEK, ↓reduceIte] at h
    sig_pre [preparedVerifyMessageContract, preparedVerifyMessageSig, RISCV64.abi, RISCV64.argRegs] at h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
      h22, h23⟩ := h
    exact ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12, h13, h15, h16, h17, h18, h19, h23⟩, h8, h14, h20,
      h22, fun _ => h21⟩

/-! ## The functions on `μ` -/

section
variable {p : Params} {stk : Nat} {x y : State}

open PreparedKey (skBytes pkBytes signEK verifyEK)

theorem sign_pre {q : Bool} {k m r g c : Addr} (g3 : x.gpr .a0 = k) (g4 : x.gpr .a1 = m) (g5 : x.gpr .a2 = r)
    (g6 : x.gpr .a3 = g) (g7 : x.gpr .a4 = c)
    (hrd : x.rd = [⟨k, skBytes p q⟩, ⟨m, 64⟩, ⟨r, 32⟩]) (hwr : x.wr = [⟨g, p.sigLen⟩, ⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0) (alc : c.toNat % 8 = 0)
    (d1 : Region.Disjoint ⟨k, skBytes p q⟩ ⟨g, p.sigLen⟩)
    (d2 : Region.Disjoint ⟨k, skBytes p q⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨m, 64⟩ ⟨g, p.sigLen⟩) (d4 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d5 : Region.Disjoint ⟨r, 32⟩ ⟨g, p.sigLen⟩) (d6 : Region.Disjoint ⟨r, 32⟩ ⟨c, scratchWords p * 8⟩)
    (d7 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, skBytes p q⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨r, 32⟩) (b4 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩)
    (b5 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (f1 : k.toNat + skBytes p q ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : r.toNat + 32 ≤ 2 ^ 64)
    (f4 : g.toNat + p.sigLen ≤ 2 ^ 64) (f5 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64)
    (hk : q = true → PreparedSecretKey p x.mem k) :
    (signEK p q stk).pre x := by
  cases q
  · simp only [signEK, skBytes, Bool.false_eq_true, ↓reduceIte] at hrd d1 d2 b1 f1 ⊢
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
  · simp only [signEK, skBytes, ↓reduceIte] at hrd d1 d2 b1 f1 ⊢
    have hk := hk rfl
    sig_pre [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs]
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

theorem sign_post {q : Bool} (hp : (signEK p q stk).post x y) :
    Outcome (fun b => signMu p b (bytesAt x.mem (x.gpr .a0) p.skLen) (bytesAt x.mem (x.gpr .a1) 64)
      (bytesAt x.mem (x.gpr .a2) 32)) ((y.gpr .a0).setWidth 32) (bytesAt y.mem (x.gpr .a3) p.sigLen) := by
  cases q
  · simp only [signEK, Bool.false_eq_true, ↓reduceIte] at hp
    sig_post [signContract, signSig, RISCV64.abi, RISCV64.argRegs] at hp
    exact hp
  · simp only [signEK, ↓reduceIte] at hp
    sig_post [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs] at hp
    exact hp

theorem sign_pub {q : Bool} (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3) (h7 : x.gpr .a4 = y.gpr .a4)
    (hl : signLeak p (bytesAt x.mem (x.gpr .a0) p.skLen) (bytesAt x.mem (x.gpr .a1) 64)
        (bytesAt x.mem (x.gpr .a2) 32) =
      signLeak p (bytesAt y.mem (y.gpr .a0) p.skLen) (bytesAt y.mem (y.gpr .a1) 64)
        (bytesAt y.mem (y.gpr .a2) 32)) :
    (signEK p q stk).pub x y := by
  cases q
  · simp only [signEK, Bool.false_eq_true, ↓reduceIte]
    sig_pub [signContract, signSig, RISCV64.abi, RISCV64.argRegs]
    exact ⟨hsp, hl, h3, h4, h5, h6, h7⟩
  · simp only [signEK, ↓reduceIte]
    sig_pub [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs]
    exact ⟨hsp, hl, h3, h4, h5, h6, h7⟩

theorem verify_pre {q : Bool} {k m g c : Addr} (g3 : x.gpr .a0 = k) (g4 : x.gpr .a1 = m) (g5 : x.gpr .a2 = g)
    (g6 : x.gpr .a3 = c)
    (hrd : x.rd = [⟨k, pkBytes p q⟩, ⟨m, 64⟩, ⟨g, p.sigLen⟩]) (hwr : x.wr = [⟨c, scratchWords p * 8⟩])
    (hsp : stk ≤ x.sp.toNat) (hal : x.sp.toNat % 16 = 0) (alc : c.toNat % 8 = 0)
    (d1 : Region.Disjoint ⟨k, pkBytes p q⟩ ⟨c, scratchWords p * 8⟩)
    (d2 : Region.Disjoint ⟨m, 64⟩ ⟨c, scratchWords p * 8⟩)
    (d3 : Region.Disjoint ⟨g, p.sigLen⟩ ⟨c, scratchWords p * 8⟩)
    (b1 : (below x.sp stk).Disjoint ⟨k, pkBytes p q⟩) (b2 : (below x.sp stk).Disjoint ⟨m, 64⟩)
    (b3 : (below x.sp stk).Disjoint ⟨g, p.sigLen⟩) (b4 : (below x.sp stk).Disjoint ⟨c, scratchWords p * 8⟩)
    (f1 : k.toNat + pkBytes p q ≤ 2 ^ 64) (f2 : m.toNat + 64 ≤ 2 ^ 64) (f3 : g.toNat + p.sigLen ≤ 2 ^ 64)
    (f4 : c.toNat + scratchWords p * 8 ≤ 2 ^ 64) (hk : q = true → PreparedPublicKey p x.mem k) :
    (verifyEK p q stk).pre x := by
  cases q
  · simp only [verifyEK, pkBytes, Bool.false_eq_true, ↓reduceIte] at hrd d1 b1 f1 ⊢
    sig_pre [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs]
    simp only [g3, g4, g5, g6]
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
  · simp only [verifyEK, pkBytes, ↓reduceIte] at hrd d1 b1 f1 ⊢
    have hk := hk rfl
    sig_pre [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs]
    simp only [g3, g4, g5, g6]
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

theorem verify_post {q : Bool} (hp : (verifyEK p q stk).post x y) :
    let v := fun b => verifyMu p b (bytesAt x.mem (x.gpr .a0) p.pkLen) (bytesAt x.mem (x.gpr .a1) 64)
      (bytesAt x.mem (x.gpr .a2) p.sigLen)
    ((y.gpr .a0).setWidth 32 = 1 ∧ ∃ b, v b = some true) ∨
      ((y.gpr .a0).setWidth 32 = 0 ∧ v minBounds ≠ some true) := by
  cases q
  · simp only [verifyEK, Bool.false_eq_true, ↓reduceIte] at hp
    sig_post [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs] at hp
    exact hp
  · simp only [verifyEK, ↓reduceIte] at hp
    sig_post [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs] at hp
    exact hp

theorem verify_pub {q : Bool} (hsp : x.sp = y.sp) (h3 : x.gpr .a0 = y.gpr .a0) (h4 : x.gpr .a1 = y.gpr .a1)
    (h5 : x.gpr .a2 = y.gpr .a2) (h6 : x.gpr .a3 = y.gpr .a3)
    (hl : bytesAt x.mem (x.gpr .a0) p.pkLen ++ bytesAt x.mem (x.gpr .a1) 64 ++ bytesAt x.mem (x.gpr .a2) p.sigLen =
      bytesAt y.mem (y.gpr .a0) p.pkLen ++ bytesAt y.mem (y.gpr .a1) 64 ++ bytesAt y.mem (y.gpr .a2) p.sigLen) :
    (verifyEK p q stk).pub x y := by
  cases q
  · simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
    sig_pub [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs]
    exact ⟨hsp, congrArg leakBytes hl, h3, h4, h5, h6⟩
  · simp only [verifyEK, ↓reduceIte]
    sig_pub [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs]
    exact ⟨hsp, congrArg leakBytes hl, h3, h4, h5, h6⟩

end

end VG.Proof.MlDsa.RISCV64.Message
