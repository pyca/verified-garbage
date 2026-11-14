module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Contract
public import VerifiedGarbage.Impl.ChaCha20Poly1305.PPC64LE
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Vmx4.Xor
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Shared
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
public import VerifiedGarbage.Proof.Poly1305.PPC64LE.Finalize
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.ChaCha20
public import VerifiedGarbage.Spec.Poly1305
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.ChaCha20.PPC64LE.Block
public import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.ChaCha20Poly1305

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
