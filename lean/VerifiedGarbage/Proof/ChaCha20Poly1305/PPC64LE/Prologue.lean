module

import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Contract
public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Vmx4.Xor
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Shared
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Finalize
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Block
public import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.ChaCha20Poly1305

/-! ### `ChaCha20Poly1305.PPC64LE.Entry`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.PPC64LE.Calls`, which only this module used -/

section

/-!
# ChaCha20-Poly1305 on PPC64LE: the calls

Each call of a verified function, from its proof (`WP.call`, or
`WP.callAny` for `vg_poly1305_blocks`, which allocates a frame): what it
needs of the state it is called from, and what holds when it returns. A
call (`bl`) stores nothing in memory, so the callee changes memory only
within the regions it may write (and its frame below the stack pointer).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Poly1305 (Repr Buffered bytesAt mac)
open VG.Spec.ChaCha20 (stateAt keystream)

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved. -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs s₂ s₃) :
    Kept rs s₁ s₃ :=
  ⟨fun r hr => by rw [h₂.cs r hr, h₁.cs r hr], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame⟩

theorem Kept.sub {rs rs' : List Region} {s s' : State} (h : Kept rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs⟩

/-! ## `vg_chacha20_block` -/

theorem block_call {s : State} {S B : Addr} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = B)
    (hdj : (⟨B, 256⟩ : Region).Disjoint ⟨S, 64⟩)
    (hc : Covers ([⟨S, 64⟩] ++ [⟨B, 256⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨B, 256⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨B, 256⟩] s s' →
      stateAt s'.mem B = Spec.ChaCha20.block (stateAt s.mem S) → Q s') :
    WP isa (.call "vg_chacha20_block" Impl.ChaCha20.PPC64LE.block) s Q := by
  refine WP.call (k := Proof.ChaCha20.blockPPC64LE) Proof.ChaCha20.PPC64LE.block_verified.1
    (rd := [⟨S, 64⟩]) (wr := [⟨B, 256⟩]) ?_ hc hw ?_
  · simp only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.ChaCha20.blockPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4] using hpost

/-! ## `vg_chacha20_xor` -/

/-- `vg_chacha20_xor` from `X` to `D` (`Proof.ChaCha20.PPC64LE.Vmx4.xor_call_to`). -/
theorem xor_call_to {s : State} {S X D B : Addr} {n : Nat} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = X)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (h6 : s.gpr .r6 = B) (h7 : s.gpr .r7 = D) (hn : n < 2 ^ 64)
    (hSX : (⟨S, 64⟩ : Region).Disjoint ⟨X, n⟩) (hSD : (⟨S, 64⟩ : Region).Disjoint ⟨D, n⟩)
    (hSB : (⟨S, 64⟩ : Region).Disjoint ⟨B, 320⟩) (hXB : (⟨X, n⟩ : Region).Disjoint ⟨B, 320⟩)
    (hDB : (⟨D, n⟩ : Region).Disjoint ⟨B, 320⟩) (hXD : D = X ∨ (⟨X, n⟩ : Region).Disjoint ⟨D, n⟩)
    (hX : X.toNat + n ≤ 2 ^ 64) (hD : D.toNat + n ≤ 2 ^ 64)
    (hc : Covers ([⟨X, n⟩] ++ [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨S, 64⟩, ⟨D, n⟩, ⟨B, 320⟩] s s' →
      Spec.ChaCha20.bytesAt s'.mem D n =
        List.zipWith (· ^^^ ·) (Spec.ChaCha20.bytesAt s.mem X n)
          (keystream (stateAt s.mem S) n) → Q s') :
    WP isa (.call "vg_chacha20_xor" Impl.ChaCha20.PPC64LE.Vmx4.xor) s Q :=
  Proof.ChaCha20.PPC64LE.Vmx4.xor_call_to h3 h4 h5 h6 h7 hn hSX hSD hSB hXB hDB hXD hX hD hc hw
    fun s' hrd hwr hsp hf hcs _ hpost => hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ hpost

/-! ## `vg_poly1305_init` -/

theorem init_call {s : State} {P K : Addr} (h3 : s.gpr .r3 = P) (h4 : s.gpr .r4 = K)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨K, 32⟩)
    (hc : Covers ([⟨K, 32⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩] s s' → Repr s'.mem P (bytesAt s.mem K 32) [] → Q s') :
    WP isa (.call "vg_poly1305_init" Impl.Poly1305.PPC64LE.init) s Q := by
  refine WP.call (k := Proof.Poly1305.initPPC64LE) Proof.Poly1305.PPC64LE.init_verified.1
    (rd := [⟨K, 32⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.initPPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4]
    exact ⟨trivial, trivial, hdj⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.Poly1305.initPPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs), h3, h4] using hpost

/-! ## `vg_poly1305_blocks`, in its frame -/

theorem blocks_call {s : State} {P p : Addr} {n : Nat} (h3 : s.gpr .r3 = P) (h4 : s.gpr .r4 = p)
    (h5 : s.gpr .r5 = BitVec.ofNat 64 n) (hn : 16 * n < 2 ^ 64) (hsp : 160 ≤ s.sp.toNat)
    (hdj : (⟨P, 128⟩ : Region).Disjoint ⟨p, 16 * n⟩)
    (hbP : (⟨s.sp - 160, 160⟩ : Region).Disjoint ⟨P, 128⟩)
    (hbp : (⟨s.sp - 160, 160⟩ : Region).Disjoint ⟨p, 16 * n⟩)
    (hP : P.toNat + 128 ≤ 2 ^ 64) (hp : p.toNat + 16 * n ≤ 2 ^ 64)
    (hc : Covers ([⟨p, 16 * n⟩] ++ [⟨P, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨s.sp - 160, 160⟩] s s' →
      (∀ key msg, Repr s.mem P key msg → Repr s'.mem P key (msg ++ bytesAt s.mem p (16 * n))) →
      Q s') :
    WP isa (.call "vg_poly1305_blocks" Impl.ChaCha20Poly1305.PPC64LE.blocksCode) s Q := by
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hn])
  refine WP.callAny (k := Proof.Poly1305.blocksContract PPC64LE.abi 160)
    Proof.Poly1305.PPC64LE.Shared.blocks.1
    (rd := [⟨p, 16 * n⟩]) (wr := [⟨P, 128⟩]) ?_ hc hw ?_
  · sig_pre [Proof.Poly1305.blocksContract, Proof.Poly1305.blocksSig, PPC64LE.abi, PPC64LE.argRegs]
    simp only [h3, h4, h5, hn', Nat.mul_comm n 16]
    exact ⟨hsp, trivial, trivial, hdj, hbP, hbp, hP, hp⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    refine hQ s' ⟨hcs, hsp', hrd, hwr, ?_⟩ fun key msg hr => ?_
    · refine hf.sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · sig_post [Proof.Poly1305.blocksContract, Proof.Poly1305.blocksSig, Proof.Poly1305.blocksPost,
        PPC64LE.abi, PPC64LE.argRegs] at hpost
      simp only [h3, h4, h5, hn'] at hpost
      exact hpost key msg hr

/-! ## `vg_poly1305_finalize_scratch` -/

theorem finalize_call {s : State} {P O Sc : Addr} {c : BitVec 64} (h3 : s.gpr .r3 = P)
    (h4 : s.gpr .r4 = c) (h5 : s.gpr .r5 = O) (h6 : s.gpr .r6 = Sc)
    (hPO : (⟨P, 128⟩ : Region).Disjoint ⟨O, 16⟩) (hPS : (⟨P, 128⟩ : Region).Disjoint ⟨Sc, 128⟩)
    (hOS : (⟨O, 16⟩ : Region).Disjoint ⟨Sc, 128⟩)
    (hc : Covers ([] ++ [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩] s s' →
      (∀ key msg, Buffered s.mem P key msg → c.toNat % 16 = msg.length % 16 →
        bytesAt s'.mem O 16 = mac key msg) → Q s') :
    WP isa (.call "vg_poly1305_finalize_scratch" Impl.Poly1305.PPC64LE.finalize) s Q := by
  refine WP.call (k := Proof.Poly1305.finalizePPC64LE) Proof.Poly1305.PPC64LE.finalize_verified.1
    (rd := []) (wr := [⟨P, 128⟩, ⟨O, 16⟩, ⟨Sc, 128⟩]) ?_ hc hw ?_
  · simp only [Proof.Poly1305.finalizePPC64LE, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r6 ∉ linkRegs), h3, h5, h6]
    exact ⟨trivial, trivial, hPO, hPS, hOS⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    refine hQ s' ⟨hcs, hsp, hrd, hwr, hf⟩ ?_
    simpa only [Proof.Poly1305.finalizePPC64LE, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.r3 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r4 ∉ linkRegs),
      State.callEntry_gpr s (by decide : Reg.r5 ∉ linkRegs), h3, h4, h5] using hpost

end VG.Proof.ChaCha20Poly1305.PPC64LE

end

end


/-!
# ChaCha20-Poly1305 on PPC64LE: the entry state, the invariant and the prologue

What the proofs use of the precondition (`APre`), the values kept in
`r24`–`r29` and our caller's registers saved in the context, and the
invariant that holds between the parts of the code (`Inv`); then the
prologue, which saves the registers, moves the arguments and stores the
ChaCha20 state for counter 0 in the context.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

section
variable (s₀ : State)
abbrev cx : Addr := s₀.gpr .r10
abbrev kp : Addr := s₀.gpr .r3
abbrev np : Addr := s₀.gpr .r4
abbrev ad : Addr := s₀.gpr .r5
abbrev AL : Nat := (s₀.gpr .r6).toNat
abbrev dp : Addr := s₀.gpr .r7
abbrev L : Nat := (s₀.gpr .r8).toNat
abbrev tp : Addr := s₀.gpr .r9
/-- The destination: `src` in place, or apart from it. -/
abbrev op : Addr := s₀.gpr .r11

abbrev K : List Byte := bytesAt s₀.mem (kp s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (np s₀) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (tp s₀) 16
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)

abbrev ctxR : Region := ⟨cx s₀, 656⟩
abbrev kR : Region := ⟨kp s₀, 32⟩
abbrev nR : Region := ⟨np s₀, 12⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev tR : Region := ⟨tp s₀, 16⟩
abbrev oR : Region := ⟨op s₀, L s₀⟩
/-- The frame of `vg_poly1305_blocks`, below the stack pointer. -/
abbrev belR : Region := ⟨s₀.sp - 160, 160⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

/-- What the proof uses of the precondition; `enc` for `seal`, which runs
in place. -/
structure APre (enc : Bool) (s₀ : State) : Prop where
  sp160 : 160 ≤ s₀.sp.toNat
  k_rd : kR s₀ ∈ s₀.rd
  n_rd : nR s₀ ∈ s₀.rd
  a_rd : aR s₀ ∈ s₀.rd
  /-- The source is readable. -/
  d_in : dR s₀ ∈ s₀.rd ++ s₀.wr
  /-- The destination is writable. -/
  o_wr : oR s₀ ∈ s₀.wr
  ctx_wr : ctxR s₀ ∈ s₀.wr
  t_in : if enc then tR s₀ ∈ s₀.wr else tR s₀ ∈ s₀.rd
  k_c : (kR s₀).Disjoint (ctxR s₀)
  n_c : (nR s₀).Disjoint (ctxR s₀)
  a_c : (aR s₀).Disjoint (ctxR s₀)
  d_c : (dR s₀).Disjoint (ctxR s₀)
  t_c : (tR s₀).Disjoint (ctxR s₀)
  k_o : (kR s₀).Disjoint (oR s₀)
  n_o : (nR s₀).Disjoint (oR s₀)
  a_o : (aR s₀).Disjoint (oR s₀)
  o_t : (oR s₀).Disjoint (tR s₀)
  o_c : (oR s₀).Disjoint (ctxR s₀)
  /-- In place, or (`open` only) apart. -/
  alias : op s₀ = dp s₀ ∨ (enc = false ∧ (dR s₀).Disjoint (oR s₀))
  enc_t : if enc then (kR s₀).Disjoint (tR s₀) ∧ (nR s₀).Disjoint (tR s₀) ∧
    (aR s₀).Disjoint (tR s₀) else True
  b_k : (belR s₀).Disjoint (kR s₀)
  b_n : (belR s₀).Disjoint (nR s₀)
  b_a : (belR s₀).Disjoint (aR s₀)
  b_d : (belR s₀).Disjoint (dR s₀)
  b_o : (belR s₀).Disjoint (oR s₀)
  b_t : (belR s₀).Disjoint (tR s₀)
  b_c : (belR s₀).Disjoint (ctxR s₀)
  fit_k : (kp s₀).toNat + 32 ≤ 2 ^ 64
  fit_n : (np s₀).toNat + 12 ≤ 2 ^ 64
  fit_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  fit_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  fit_o : (op s₀).toNat + L s₀ ≤ 2 ^ 64
  fit_t : (tp s₀).toNat + 16 ≤ 2 ^ 64
  fit_c : (cx s₀).toNat + 656 ≤ 2 ^ 64

variable {e : Bool}

theorem APre.t_wr {s₀ : State} (hp : APre true s₀) : tR s₀ ∈ s₀.wr := hp.t_in

theorem APre.t_rd {s₀ : State} (hp : APre false s₀) : tR s₀ ∈ s₀.rd := hp.t_in

/-- `seal` runs in place. -/
theorem APre.inPlace {s₀ : State} (hp : APre true s₀) : op s₀ = dp s₀ := by
  rcases hp.alias with h | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 656) : Region.Sub (sub s₀ k n) (ctxR s₀) :=
  Offset.sub_base _ h

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 656)
    (hb : b + m ≤ 656) : (sub s₀ a n).Disjoint (sub s₀ b m) :=
  Offset.disjoint (cx s₀) h (by omega_using [ha]) (by omega_using [hb])

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 656) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := Offset.contains (cx s₀) h₁ h₂ (by omega_using [h₃])

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 656) : (ctxR s₀).Contains (off (cx s₀) a) w :=
  Offset.contains_base (cx s₀) h (by omega_using [h])

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

theorem sub_zero (s₀ : State) (n : Nat) : sub s₀ 0 n = ⟨cx s₀, n⟩ := by simp [sub, off]

namespace APre
variable {s₀ : State} (hp : APre e s₀)
include hp

theorem in_ctx {a w : Nat} (h : a + w ≤ 656) : InRegions s₀.wr (off (cx s₀) a) w :=
  ⟨ctxR s₀, hp.ctx_wr, contains_ctx s₀ h⟩

theorem in_ctx' {a w : Nat} (h : a + w ≤ 656) : InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w :=
  ⟨ctxR s₀, List.mem_append_right _ hp.ctx_wr, contains_ctx s₀ h⟩

theorem k_in {d : Nat} (h : d + 4 ≤ 32) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (off (kp s₀) d) 4 :=
  ⟨kR s₀, by rw [hrd]; exact List.mem_append_left _ hp.k_rd, Offset.contains_base _ h (by omega_using [h])⟩

theorem n_in {d : Nat} (h : d + 4 ≤ 12) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (off (np s₀) d) 4 :=
  ⟨nR s₀, by rw [hrd]; exact List.mem_append_left _ hp.n_rd, Offset.contains_base _ h (by omega_using [h])⟩

end APre

/-! ## The saved registers and the invariant -/

/-- Our caller's `r24`–`r29` and `r31`, and our return address, saved in
`ctx[464, 528)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  (∀ i < 7, m.readW (off (cx s₀) (savOff + 8 * i)) 64 = s₀.gpr (saved i)) ∧
    m.readW (off (cx s₀) (savOff + 56)) 64 = s₀.lr

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ savOff 64).Disjoint r) : Saved s₀ m' := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hf.readW (contains_sub s₀ (w := 64 / 8) (by simp only [savOff]; omega_using [])
      (by simp only [savOff]; omega_using [hi]) (by decide)) hd (by decide), h.1 i hi]
  · rw [hf.readW (contains_sub s₀ (w := 64 / 8) (by simp only [savOff]; omega_using [])
      (by simp only [savOff]; omega_using []) (by decide)) hd (by decide), h.2]

/-- The values we keep in `r24`–`r29` and `r31`. -/
structure Regs (s₀ s : State) : Prop where
  r24 : s.gpr .r24 = cx s₀
  r25 : s.gpr .r25 = s₀.gpr .r5
  r26 : s.gpr .r26 = s₀.gpr .r6
  r27 : s.gpr .r27 = s₀.gpr .r7
  r28 : s.gpr .r28 = s₀.gpr .r8
  r29 : s.gpr .r29 = s₀.gpr .r9
  r31 : s.gpr .r31 = s₀.gpr .r11

theorem Regs.kept {s₀ s s' : State} (h : Regs s₀ s) (hk : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Regs s₀ s' :=
  ⟨by rw [hk _ (by decide), h.r24], by rw [hk _ (by decide), h.r25],
    by rw [hk _ (by decide), h.r26], by rw [hk _ (by decide), h.r27],
    by rw [hk _ (by decide), h.r28], by rw [hk _ (by decide), h.r29], by rw [hk _ (by decide), h.r31]⟩

/-- What holds between the parts of the code: the registers, the stack
pointer and the regions, the saved registers, and the memory changed only
in the context, the destination and the stack below the stack pointer. -/
structure Inv (s₀ : State) (s : State) : Prop where
  regs : Regs s₀ s
  pres : ∀ r ∈ preserved, (∀ i < 7, r ≠ saved i) → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [ctxR s₀, oR s₀, belR s₀] s₀.mem s.mem

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the context outside the saved registers, the destination and the stack
below the stack pointer. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : Inv s₀ s) (hk : Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [ctxR s₀, oR s₀, belR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ savOff 64).Disjoint r) : Inv s₀ s' where
  regs := h.regs.kept hk.cs
  pres r hr hne := by rw [hk.cs r hr, h.pres r hr hne]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- A part that writes `ctx[k, k + n)` keeps the invariant. -/
theorem Inv.step1 {s₀ s s' : State} (h : Inv s₀ s) {k n : Nat} (hk : Kept [sub s₀ k n] s s')
    (h₂ : k + n ≤ 656) (h₃ : k + n ≤ savOff ∨ savOff + 64 ≤ k) : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ctxR s₀, by simp, sub_ctx s₀ h₂⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by simp only [savOff] at h₃ ⊢; omega_using [h₃]) (by decide) h₂)

/-- A part that writes no memory keeps the invariant. -/
theorem Inv.step0 {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept [] s s') : Inv s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

/-- The context may be read and written. -/
def CtxOk (s₀ s : State) : Prop :=
  ∀ a w, a + w ≤ 656 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) w ∧ InRegions s.wr (off (cx s₀) a) w

theorem Inv.ctxOk {s₀ s : State} (hp : APre e s₀) (h : s.rd = s₀.rd) (h' : s.wr = s₀.wr) : CtxOk s₀ s :=
  fun _ _ hw => by rw [h, h']; exact ⟨hp.in_ctx' hw, hp.in_ctx hw⟩

theorem Kept.mem_eq {s s' : State} (hk : Kept [] s s') : s'.mem = s.mem :=
  funext fun x => hk.frame x fun _ h => absurd h List.not_mem_nil

end VG.Proof.ChaCha20Poly1305.PPC64LE

end

end

/-!
# ChaCha20-Poly1305 on PPC64LE: the prologue

Saving the registers, moving the arguments, the ChaCha20 state for counter
0, the one-time key and the Poly1305 state for it; and what the later parts
use of memory and of the callees' regions.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt)

variable {e : Bool}

theorem savOff_eq : savOff = 464 := rfl
theorem stOff_eq : stOff = 320 := rfl
/-- A register not callee-saved is not a callee-saved one. -/
theorem ne_of_pres {r d : Reg} (hr : r ∈ preserved) (hd : d ∉ preserved := by decide) : r ≠ d := by
  rintro rfl; exact hd hr

/-! ## Memory -/

theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := off_off p a b

/-- A read at `p + d` after a write at `p + e`, elsewhere. -/
theorem readW_writeW_off (m : Mem) (p : Addr) {w w' : Nat} (v : BitVec w') {d e : Nat}
    (hd : d + w / 8 ≤ 2 ^ 64) (he : e + w' / 8 ≤ 2 ^ 64) (h : d + w / 8 ≤ e ∨ e + w' / 8 ≤ d)
    (hw : w / 8 < 2 ^ 64 := by decide) :
    (m.writeW (off p e) v).readW (off p d) w = m.readW (off p d) w :=
  Mem.readW_writeW_sep (Offset.sep p h hd he) hw

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A Poly1305 state outside a frame is unchanged. -/
theorem Repr.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte} (h : Repr m P key msg) :
    Repr m' P key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (Offset.sub_base P (d := 24) (by decide)))
      (by decide)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))
      (by decide)]
    exact h3

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])) hd (by decide)

/-- Byte `i` of a little-endian doubleword. -/
theorem readW64_byte (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    m (a + BitVec.ofNat 64 i) = (m.readW a 64).extractLsb' (8 * i) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  simp only [Mem.readW]
  rfl

/-- Bytes equal byte by byte. -/
theorem bytesAt_eq_of {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ i < n, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    bytesAt m' q n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.ext_getElem (by simp)
  intro i h₁ _
  simp only [List.getElem_map, List.getElem_range]
  exact h i (by simpa using h₁)

/-- Doublewords copied are bytes copied. -/
theorem bytes_of_dwords {m m' : Mem} {p q : Addr} {n : Nat}
    (h : ∀ k < n, m'.readW (q + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64) :
    bytesAt m' q (8 * n) = bytesAt m p (8 * n) := by
  refine bytesAt_eq_of fun i hi => ?_
  have e : ∀ a : Addr, a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
    intro a
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod]
  rw [e, e, readW64_byte m' _ (Nat.mod_lt _ (by decide)), readW64_byte m _ (Nat.mod_lt _ (by decide)),
    h _ (by omega_using [hi])]

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega_using [hn]
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by omega_using [hn, h₁])
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega_using [hn, h₁]), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

/-! ## Covering the callees' regions -/

theorem covers_right {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun a n hi =>
  let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_sub {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r = sub s₀ k r.len ∧ k + r.len ≤ 656) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hrk, hk⟩ := h r hr
  exact ⟨ctxR s₀, by rw [hwr]; exact hp.ctx_wr, k, by rw [hrk], hk⟩

/-- A callee's working space (at `ctx + a`, `n` bytes) and argument (at
`ctx + b`, `m` bytes) in the context. -/
theorem covers2 {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) {a n b m : Nat}
    (ha : a + n ≤ 656) (hb : b + m ≤ 656) :
    Covers ([sub s₀ b m] ++ [sub s₀ a n]) (s.rd ++ s.wr) :=
  covers_right (covers_sub hp hwr _ fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨b, rfl, hb⟩
    · exact ⟨a, rfl, ha⟩)

theorem covers1 {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) {a n : Nat} (ha : a + n ≤ 656) :
    Covers [sub s₀ a n] s.wr :=
  covers_sub hp hwr _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨a, rfl, ha⟩

/-! ## Saving the registers -/

/-- The first `n` registers saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sub s₀ savOff 64] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (cx s₀) (savOff + 8 * i)) 64 = s₀.gpr (saved i)

theorem save_step {s₀ : State} (hp : APre e s₀) {n : Nat} (hn : n < 7) {s : State} (h : SI s₀ n s) :
    WP isa (.block [.store .d (saved n) .r10 (savOff + 8 * n)]) s (SI s₀ (n + 1)) := by
  refine wp_std (a := off (cx s₀) (savOff + 8 * n)) (by decide) (by rw [savOff_eq]; omega_using [hn])
    (by rw [h.gpr]) (by rw [h.wr]; exact hp.in_ctx (by rw [savOff_eq]; omega_using [hn])) fun s' u => WP.block_nil ?_
  refine ⟨by rw [u.gpr, h.gpr], by rw [u.sp, h.sp], by rw [u.lr, h.lr], by rw [u.rd, h.rd],
    by rw [u.wr, h.wr], ?_, fun i hi => ?_⟩
  · rw [u.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega_using []) (by omega_using [hn]) (by decide))
  · rw [u.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [readW_writeW_off _ _ _ (by rw [savOff_eq]; omega_arith) (by rw [savOff_eq]; omega_using [hn]) (by omega_using [hi])]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-- Saving the registers and the return address. -/
theorem save_ok {s₀ : State} (hp : APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, (∀ r, r ≠ .r0 → s.gpr r = s₀.gpr r) → s.sp = s₀.sp → s.rd = s₀.rd → s.wr = s₀.wr →
      Saved s₀ s.mem → Frame [sub s₀ savOff 64] s₀.mem s.mem → WP isa (.block rest) s Q) :
    WP isa (.block (save ++ rest)) s₀ Q := by
  rw [save, List.append_assoc]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step hp hk h) 7 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  refine wp_mflr fun s₁ u₁ => ?_
  refine wp_std (a := off (cx s₀) (savOff + 56)) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), h.gpr]) (by rw [u₁.wr, h.wr]; exact hp.in_ctx (by decide))
    fun s₂ u₂ => ?_
  refine k s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr, h.gpr]) (by rw [u₂.sp, u₁.sp, h.sp])
    (by rw [u₂.rd, u₁.rd, h.rd]) (by rw [u₂.wr, u₁.wr, h.wr]) ⟨fun i hi => ?_, ?_⟩ ?_
  · rw [u₂.mem, readW_writeW_off _ _ _ (by rw [savOff_eq]; omega_using [hi]) (by decide) (by omega_using [hi]), u₁.mem]
    exact h.saved i hi
  · rw [u₂.mem, Mem.readW_writeW_self64, u₁.gpr, h.lr]
  · rw [u₂.mem, u₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 64 / 8) (by omega_using []) (by omega_using []) (by decide))

/-! ## Moving the arguments -/

theorem moves_ok {s₀ s : State} (hg : ∀ r, r ≠ .r0 → s.gpr r = s₀.gpr r) :
    WP isa (.block moves) s fun s' => Regs s₀ s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧ ∀ r, (∀ i < 7, r ≠ saved i) → s'.gpr r = s.gpr r := by
  unfold moves
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · intro r hr
    rw [u₇.other r (hr 6 (by decide)), u₆.other r (hr 5 (by decide)), u₅.other r (hr 4 (by decide)),
      u₄.other r (hr 3 (by decide)), u₃.other r (hr 2 (by decide)), u₂.other r (hr 1 (by decide)),
      u₁.other r (hr 0 (by decide))]

/-- Saving the registers and moving the arguments. -/
theorem saveMoves_ok {s₀ : State} (hp : APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, Regs s₀ s → (∀ r, (∀ i < 7, r ≠ saved i) → r ≠ .r0 → s.gpr r = s₀.gpr r) →
      s.gpr .r3 = kp s₀ → s.gpr .r4 = np s₀ → s.sp = s₀.sp → s.rd = s₀.rd →
      s.wr = s₀.wr → Saved s₀ s.mem → Frame [sub s₀ savOff 64] s₀.mem s.mem → WP isa (.block rest) s Q) :
    WP isa (.block (save ++ moves ++ rest)) s₀ Q := by
  rw [List.append_assoc]
  refine save_ok hp fun s₁ g₁ sp₁ rd₁ wr₁ sv₁ f₁ => ?_
  refine WP.block_append (WP.mono (moves_ok g₁) fun s₂ ⟨rg, m₂, rd₂, wr₂, sp₂, o₂⟩ => ?_)
  refine k s₂ rg (fun r hr h0 => by rw [o₂ r hr, g₁ r h0]) ?_ ?_ (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [m₂]; exact sv₁)
    (by rw [m₂]; exact f₁)
  · rw [o₂ _ (by decide), g₁ _ (by decide)]
  · rw [o₂ _ (by decide), g₁ _ (by decide)]

/-! ## Copying doublewords of the context -/

theorem copyWords_step (a b n : Nat) : copyWords a b (n + 1) =
    copyWords a b n ++ ([.load .d .r12 .r24 (a + 8 * n), .store .d .r12 .r24 (b + 8 * n)] : List Instr) := by
  simp [copyWords, List.range_succ, List.flatMap_append]

/-- `n` doublewords from `ctx + a` to `ctx + b`. -/
theorem copyWords_ok {s₀ : State} {a b n : Nat} (hab : a + 8 * n ≤ b ∨ b + 8 * n ≤ a)
    (ha : a + 8 * n ≤ 656) (hb : b + 8 * n ≤ 656) (ha4 : a % 4 = 0) (hb4 : b % 4 = 0) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (hc : CtxOk s₀ s) :
    WP isa (.block (copyWords a b n)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ b (8 * n)] s.mem s'.mem ∧
      ∀ i < n, s'.mem.readW (off (cx s₀) (b + 8 * i)) 64 = s.mem.readW (off (cx s₀) (a + 8 * i)) 64 := by
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_using [])⟩
  | succ n ih =>
    rw [copyWords_step]
    refine WP.block_append (WP.mono (ih (by omega_using [hab]) (by omega_using [ha]) (by omega_using [hb]))
      fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk s₀ s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    have h14₁ : s₁.gpr .r24 = cx s₀ := by rw [g₁ _ (by decide), h14]
    refine wp_ld (a := off (cx s₀) (a + 8 * n)) (by decide) (by omega_using [ha4, ha]) (by rw [h14₁])
      (hc₁ _ 8 (by omega_using [ha])).1 fun s₂ u₂ => ?_
    refine wp_std (a := off (cx s₀) (b + 8 * n)) (by decide) (by omega_using [hb4, hb])
      (by rw [u₂.other _ (by decide), h14₁]) (by rw [u₂.wr]; exact (hc₁ _ 8 (by omega_using [hb])).2)
      fun s₃ u₃ => WP.block_nil ?_
    refine ⟨fun r hr => by rw [u₃.gpr, u₂.other r hr, g₁ r hr], by rw [u₃.rd, u₂.rd, rd₁],
      by rw [u₃.wr, u₂.wr, wr₁], by rw [u₃.sp, u₂.sp, sp₁], ?_, fun i hi => ?_⟩
    · rw [u₃.mem, u₂.mem]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact Region.sub_prefix (by omega_using [])
      · exact contains_sub s₀ (w := 64 / 8) (by omega_using []) (by omega_using []) (by omega_using [hb])
    · rw [u₃.mem, u₂.gpr, u₂.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [readW_writeW_off _ _ _ (by omega_arith) (by omega_using [hb]) (by omega_using [hi]), w₁ i hi]
      · rw [Mem.readW_writeW_self64]
        exact f₁.readW (contains_sub s₀ (k := a + 8 * i) (n := 8) (w := 64 / 8) (Nat.le_refl _) (by omega_using [])
            (by omega_using [ha]))
          (by simp only [List.mem_singleton, forall_eq]; exact sub_disj s₀ (by omega_using [hab]) (by omega_using [ha]) (by omega_using [hb]))
          (by decide)

/-! ## The ChaCha20 state -/

/-- The word `stW k` stores, from memory `m`, the key at `kp` and the nonce at `np`. -/
def wordOf (m : Mem) (kp np : Addr) (k : Nat) : BitVec 32 :=
  if k < 4 then consts.getD k 0
  else if k < 12 then m.readW (off kp (4 * (k - 4))) 32
  else if k = 12 then 0
  else m.readW (off np (4 * (k - 13))) 32

theorem sw32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

theorem stW_ok {s₀ : State} (hp : APre e s₀) {k : Nat} (hk : k < 16) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (h3 : s.gpr .r3 = kp s₀) (h4 : s.gpr .r4 = np s₀) (hrd : s.rd = s₀.rd)
    (hc : CtxOk s₀ s) :
    WP isa (.block (stW k)) s fun s' =>
      s'.mem = s.mem.writeW (off (cx s₀) (stOff + 4 * k)) (wordOf s.mem (kp s₀) (np s₀) k) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have o := (hc (stOff + 4 * k) 4 (by rw [stOff_eq]; omega_using [hk])).2
  have ho : stOff + 4 * k < 2 ^ 15 := by rw [stOff_eq]; omega_using [hk]
  unfold stW stSrc wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true, List.cons_append, List.nil_append]
    refine wp_lis fun s₁ u₁ => wp_ori fun s₂ u₂ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h14]) (by rw [u₂.wr, u₁.wr]; exact o)
      fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, lis_ori], fun r hr => by
      rw [g₃.gpr, u₂.other r hr, u₁.other r hr], by rw [g₃.rd, u₂.rd, u₁.rd], by rw [g₃.wr, u₂.wr, u₁.wr],
      by rw [g₃.sp, u₂.sp, u₁.sp]⟩
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false, List.cons_append, List.nil_append]
    refine wp_lwz (a := off (kp s₀) (4 * (k - 4))) (by decide) (by omega_using [hk]) (by rw [h3])
      (hp.k_in (by omega_using [h₂]) hrd) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, sw32], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  by_cases h₃ : k = 12
  · subst h₃
    simp only [ite_true]
    refine wp_li (by decide) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * 12)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem]; rfl, fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩
  · simp only [h₁, h₂, h₃, ite_false, List.cons_append, List.nil_append]
    refine wp_lwz (a := off (np s₀) (4 * (k - 13))) (by decide) (by omega_using [hk]) (by rw [h4])
      (hp.n_in (by omega_using [hk]) hrd) fun s₁ u₁ => ?_
    refine wp_stw (a := off (cx s₀) (stOff + 4 * k)) (by decide) ho
      (by rw [u₁.other _ (by decide), h14]) (by rw [u₁.wr]; exact o) fun s₃ g₃ => WP.block_nil ?_
    refine ⟨by rw [g₃.mem, u₁.gpr, u₁.mem, sw32], fun r hr => by rw [g₃.gpr, u₁.other r hr],
      by rw [g₃.rd, u₁.rd], by rw [g₃.wr, u₁.wr], by rw [g₃.sp, u₁.sp]⟩

/-- A frame of `ctx[k, k + n)` is one of the context. -/
theorem frame_ctx {s₀ : State} {m m' : Mem} {k n : Nat} (hf : Frame [sub s₀ k n] m m') (h : k + n ≤ 656) :
    Frame [ctxR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨ctxR s₀, List.mem_singleton_self _, sub_ctx s₀ h⟩

/-- Words outside the context are unchanged by a frame of the context. -/
theorem readW_out {s₀ : State} {m m' : Mem} (hf : Frame [ctxR s₀] m m') {p : Addr} {n : Nat}
    (hd : (ctxR s₀).Disjoint ⟨p, n⟩) {a : Nat} (ha : a + 4 ≤ n) :
    m'.readW (off p a) 32 = m.readW (off p a) 32 :=
  hf.readW (r := ⟨off p a, 4⟩) (Region.contains_self _ _)
    (by simp only [List.mem_singleton, forall_eq]; exact (hd.sub_right (Offset.sub_base p (d := a) (n := 4) ha)).symm)
    (by decide)

theorem wordOf_frame {s₀ : State} (hp : APre e s₀) {m m' : Mem} (hf : Frame [ctxR s₀] m m') {k : Nat}
    (hk : k < 16) :
    wordOf m' (kp s₀) (np s₀) k = wordOf m (kp s₀) (np s₀) k := by
  unfold wordOf
  by_cases h₁ : k < 4
  · simp only [h₁, ite_true]
  by_cases h₂ : k < 12
  · simp only [h₁, h₂, ite_true, ite_false]; exact readW_out hf hp.k_c.symm (by omega_using [h₂])
  by_cases h₃ : k = 12
  · subst h₃; simp only [h₁, h₂, ite_true, ite_false]
  · simp only [h₁, h₂, h₃, ite_false]; exact readW_out hf hp.n_c.symm (by omega_using [hk])

theorem initState_step (j : Nat) : (List.range (j + 1)).flatMap stW = (List.range j).flatMap stW ++ stW j := by
  simp [List.range_succ, List.flatMap_append]

/-- The first `j` words of the ChaCha20 state. -/
theorem initState_ok {s₀ : State} (hp : APre e s₀) {j : Nat} (hj : j ≤ 16) {s : State}
    (h14 : s.gpr .r24 = cx s₀) (h3 : s.gpr .r3 = kp s₀) (h4 : s.gpr .r4 = np s₀) (hrd : s.rd = s₀.rd)
    (hc : CtxOk s₀ s) :
    WP isa (.block ((List.range j).flatMap stW)) s fun s' =>
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [sub s₀ stOff (4 * j)] s.mem s'.mem ∧
      ∀ i < j, s'.mem.readW (off (cx s₀) (stOff + 4 * i)) 32 = wordOf s.mem (kp s₀) (np s₀) i := by
  induction j with
  | zero =>
    exact WP.block_nil (M := isa) ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_using [])⟩
  | succ j ih =>
    rw [initState_step]
    refine WP.block_append (WP.mono (ih (by omega_using [hj])) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, f₁, w₁⟩ => ?_)
    have hc₁ : CtxOk s₀ s₁ := by rw [CtxOk, rd₁, wr₁]; exact hc
    refine WP.mono (stW_ok hp (by omega_using [hj]) (by rw [g₁ _ (by decide), h14]) (by rw [g₁ _ (by decide), h3])
      (by rw [g₁ _ (by decide), h4]) (by rw [rd₁, hrd]) hc₁)
      fun s₂ ⟨m₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
    refine ⟨fun r hr => by rw [g₂ r hr, g₁ r hr], by rw [rd₂, rd₁], by rw [wr₂, wr₁], by rw [sp₂, sp₁],
      ?_, fun i hi => ?_⟩
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_using [])
      · exact contains_sub s₀ (w := 32 / 8) (by omega_using []) (by omega_using []) (by rw [stOff_eq]; omega_using [hj])
    · rw [m₂, wordOf_frame hp (frame_ctx f₁ (by rw [stOff_eq]; omega_using [hj])) (k := j) (by omega_using [hj])]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [readW_writeW_off _ _ _ (by rw [stOff_eq]; omega_arith) (by rw [stOff_eq]; omega_using [hj]) (by omega_using [hi])]
        exact w₁ i hi
      · exact Mem.readW_writeW_self32 _ _ _

theorem consts_eq : ∀ i < 4, consts.getD i 0 = Spec.ChaCha20.constants.getD i 0 := by decide +kernel

/-- The words stored are the initial ChaCha20 state for the key, counter 0
and the nonce, if the key and the nonce are as on entry. -/
theorem stateAt_initState {s₀ : State} (hp : APre e s₀) {m₁ m' : Mem} (hf₁ : Frame [ctxR s₀] s₀.mem m₁)
    (hw : ∀ i < 16, m'.readW (off (cx s₀) (stOff + 4 * i)) 32 = wordOf m₁ (kp s₀) (np s₀) i) :
    stateAt m' (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Spec.ChaCha20.initState, Vector.getElem_ofFn]
  rw [off_add, hw i hi, wordOf_frame hp hf₁ hi]
  unfold wordOf
  by_cases h₁ : i < 4
  · simp only [h₁, ite_true]; exact consts_eq i h₁
  by_cases h₂ : i < 12
  · simp only [h₁, h₂, ite_true, ite_false]
    rw [show (K s₀) = Spec.ChaCha20.bytesAt s₀.mem (kp s₀) 32 from rfl,
      wordLE_bytesAt s₀.mem (kp s₀) (n := 32) (j := i - 4) (by omega_using [h₂])]
  by_cases h₃ : i = 12
  · subst h₃; simp only [h₁, h₂, ite_true, ite_false]
  · simp only [h₁, h₂, h₃, ite_false]
    rw [show (N s₀) = Spec.ChaCha20.bytesAt s₀.mem (np s₀) 12 from rfl,
      wordLE_bytesAt s₀.mem (np s₀) (n := 12) (j := i - 13) (by omega_using [hi])]

/-! ## The first block -/

/-- After the first block: the registers saved and moved, and the ChaCha20
state. -/
structure Post1 (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  fctx : Frame [ctxR s₀] s₀.mem s.mem

/-- The first block of both functions. -/
theorem block1_ok {s₀ : State} (hp : APre e s₀) :
    WP isa (.block (save ++ moves ++ initState)) s₀ (Post1 s₀) := by
  refine saveMoves_ok hp fun s₁ rg og h3 h4 sp rd wr sv f₁ => ?_
  have i₁ : Inv s₀ s₁ := ⟨rg, fun r hr hne => og r hne (ne_of_pres hr), sp, rd, wr, sv, f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ctxR s₀, List.mem_cons_self, sub_ctx s₀ (by decide)⟩⟩
  have hf₁ := frame_ctx f₁ (by decide)
  refine WP.mono (initState_ok hp (j := 16) (Nat.le_refl _) rg.r24 h3 h4 rd (Inv.ctxOk hp rd wr))
    fun s₂ ⟨g₂, rd₂, wr₂, sp₂, f₂, w₂⟩ => ⟨?_, ?_, hf₁.trans (frame_ctx f₂ (by decide))⟩
  · exact i₁.step1 ⟨fun r hr => g₂ r (ne_of_pres hr), sp₂, rd₂, wr₂, f₂⟩ (by decide) (by decide)
  · exact stateAt_initState hp hf₁ w₂

/-! ## The one-time key -/

/-- `r3 = ctx + stOff`, `r4 = ctx`. -/
theorem kgA_ok {s₀ s : State} (h : Inv s₀ s) :
    WP isa (.block [.addi .r3 .r24 stOff, mov .r4 .r24]) s fun s' =>
      s'.gpr .r3 = off (cx s₀) stOff ∧ s'.gpr .r4 = cx s₀ ∧ Kept [] s s' :=
  wp_addi (by decide) (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, h.regs.r24], by rw [u₂.gpr, u₁.other _ (by decide), h.regs.r24],
      ⟨fun r hr => by rw [u₂.other r (ne_of_pres hr), u₁.other r (ne_of_pres hr)], by rw [u₂.sp, u₁.sp],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩⟩

/-- After the one-time key is computed. -/
structure PostK (s₀ : State) (s : State) : Prop where
  inv : Inv s₀ s
  st : stateAt s.mem (off (cx s₀) stOff) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)
  key : bytesAt s.mem (off (cx s₀) keyOff) 32 = otk s₀

theorem keyGen_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Post1 s₀ s) :
    WP isa keyGen s fun s' => PostK s₀ s' ∧ Frame [sub s₀ 0 256, sub s₀ keyOff 32] s.mem s'.mem := by
  unfold keyGen
  refine WP.seq (WP.mono (kgA_ok h.inv) fun s₁ ⟨h3, h4, k₁⟩ => ?_)
  have i₁ := h.inv.step0 k₁
  have m₁ := k₁.mem_eq
  have dj : (⟨cx s₀, 256⟩ : Region).Disjoint ⟨off (cx s₀) stOff, 64⟩ := by
    rw [← sub_zero s₀ 256]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have cv : Covers ([(⟨off (cx s₀) stOff, 64⟩ : Region)] ++ [⟨cx s₀, 256⟩]) (s₁.rd ++ s₁.wr) := by
    rw [← sub_zero s₀ 256]; exact covers2 hp i₁.wr (by decide) (by decide)
  have cw : Covers [(⟨cx s₀, 256⟩ : Region)] s₁.wr := by
    rw [← sub_zero s₀ 256]; exact covers1 hp i₁.wr (by decide)
  refine WP.seq (block_call h3 h4 dj cv cw fun s₂ k₂ blk₂ => ?_)
  rw [← sub_zero s₀ 256] at k₂
  have i₂ := i₁.step1 k₂ (by decide) (by decide)
  refine WP.mono (copyWords_ok (a := 0) (b := keyOff) (n := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) i₂.regs.r24 (Inv.ctxOk hp i₂.rd i₂.wr))
    fun s₃ ⟨g₃, rd₃, wr₃, sp₃, f₃, w₃⟩ => ?_
  have hk₃ : Kept [sub s₀ keyOff (8 * 4)] s₂ s₃ := ⟨fun r hr => g₃ r (ne_of_pres hr), sp₃, rd₃, wr₃, f₃⟩
  refine ⟨⟨i₂.step1 hk₃ (by decide) (by decide), ?_, ?_⟩, ?_⟩
  · -- The ChaCha20 state is outside both writes.
    rw [stateAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by decide) (by decide) (by decide)),
      stateAt_frame k₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (a := stOff) (n := 64) (b := 0) (m := 256) (by decide) (by decide)
          (by decide)), m₁, h.st]
  · have e : bytesAt s₃.mem (off (cx s₀) keyOff) (8 * 4) = bytesAt s₂.mem (off (cx s₀) 0) (8 * 4) :=
      bytes_of_dwords fun k hk => by rw [off_add, off_add]; exact w₃ k hk
    rw [show (32 : Nat) = 8 * 4 from rfl, e, off_zero, bytesAt_serialize _ _ (by decide), blk₂, m₁, h.st]
    rfl
  · refine (k₁.frame.sub fun _ hr => absurd hr List.not_mem_nil).trans ((k₂.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact f₃.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩

/-! ## The Poly1305 state -/

/-- `r3 = ctx`, `r4 = ctx + keyOff`. -/
theorem piA_ok {s₀ s : State} (h : Inv s₀ s) :
    WP isa (.block [mov .r3 .r24, .addi .r4 .r24 keyOff]) s fun s' =>
      s'.gpr .r3 = cx s₀ ∧ s'.gpr .r4 = off (cx s₀) keyOff ∧ Kept [] s s' :=
  wp_mov fun s₁ u₁ => wp_addi (by decide) (by decide) fun s₂ u₂ => WP.block_nil
    ⟨by rw [u₂.other _ (by decide), u₁.gpr, h.regs.r24], by rw [u₂.gpr, u₁.other _ (by decide), h.regs.r24],
      ⟨fun r hr => by rw [u₂.other r (ne_of_pres hr), u₁.other r (ne_of_pres hr)], by rw [u₂.sp, u₁.sp],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _⟩⟩

theorem polyInit_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hkey : bytesAt s.mem (off (cx s₀) keyOff) 32 = otk s₀) :
    WP isa polyInit s fun s' => Inv s₀ s' ∧ Kept [sub s₀ 0 128] s s' ∧ Repr s'.mem (cx s₀) (otk s₀) [] := by
  unfold polyInit
  refine WP.seq (WP.mono (piA_ok h) fun s₁ ⟨h3, h4, k₁⟩ => ?_)
  have i₁ := h.step0 k₁
  have dj : (⟨cx s₀, 128⟩ : Region).Disjoint ⟨off (cx s₀) keyOff, 32⟩ := by
    rw [← sub_zero s₀ 128]; exact sub_disj s₀ (by decide) (by decide) (by decide)
  have cv : Covers ([(⟨off (cx s₀) keyOff, 32⟩ : Region)] ++ [⟨cx s₀, 128⟩]) (s₁.rd ++ s₁.wr) := by
    rw [← sub_zero s₀ 128]; exact covers2 hp i₁.wr (by decide) (by decide)
  have cw : Covers [(⟨cx s₀, 128⟩ : Region)] s₁.wr := by
    rw [← sub_zero s₀ 128]; exact covers1 hp i₁.wr (by decide)
  refine init_call h3 h4 dj cv cw fun s₂ k₂ repr₂ => ?_
  rw [← sub_zero s₀ 128] at k₂
  refine ⟨i₁.step1 k₂ (by decide) (by decide), (k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂, ?_⟩
  rw [k₁.mem_eq, hkey] at repr₂
  exact repr₂

end VG.Proof.ChaCha20Poly1305.PPC64LE
