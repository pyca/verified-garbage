import VerifiedGarbage.Proof.Poly1305.X86_64.Finalize
import VerifiedGarbage.Proof.Poly1305.X86_64.Variant
import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Update`. -/
section

/-!
# Poly1305 on x86-64: `update`, up to the call

The contract `update` is proven against, and its code up to the call of
`vg_poly1305_blocks` (`updatePre`): saving the caller's registers in
`scratch`, filling the buffer and absorbing it once full, and setting up the
call.
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305 (bytesAt Buffered)

open VG.X86_64 in
/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len:
usize, scratch: *mut [u64; 16])`: only `count mod 16`, the number of bytes
buffered, matters. The call of `vg_poly1305_blocks` uses the 24 bytes of stack
below the return address (its return address, and up to 16 bytes for its own
calls, see `BlocksImpl`). -/
def updateX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 128⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 128⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .rdi) key msg →
    (s.gpr .rsi).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .rdi) key (msg ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Poly1305

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev dp : Addr := s₀.gpr .rdx
abbrev dl : Nat := (s₀.gpr .rcx).toNat
abbrev dR : Region := ⟨VG.Proof.Poly1305.X86_64.dp s₀, VG.Proof.Poly1305.X86_64.dl s₀⟩
/-- The number of bytes buffered. -/
abbrev kb : Nat := (s₀.gpr .rsi).toNat % 16
/-- The bytes buffered. -/
abbrev Bf : List Byte := bytesAt s₀.mem (off (st s₀) 56) (VG.Proof.Poly1305.X86_64.kb s₀)
/-- The first `c` bytes of data. -/
abbrev Dt (c : Nat) : List Byte := bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.dp s₀) c
/-- The working space. -/
abbrev scr : Addr := s₀.gpr .r8
abbrev scR : Region := ⟨VG.Proof.Poly1305.X86_64.scr s₀, 128⟩
/-- The stack below the return address that the call uses. -/
abbrev stkR : Region := ⟨s₀.gpr .rsp - 24, 24⟩
end

structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Poly1305.X86_64.dR s₀]
  wr : s₀.wr = [sR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀]
  st_sc : (sR (st s₀)).Disjoint (VG.Proof.Poly1305.X86_64.scR s₀)
  d_st : (VG.Proof.Poly1305.X86_64.dR s₀).Disjoint (sR (st s₀))
  d_sc : (VG.Proof.Poly1305.X86_64.dR s₀).Disjoint (VG.Proof.Poly1305.X86_64.scR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  ret_sc : (retR s₀).Disjoint (VG.Proof.Poly1305.X86_64.scR s₀)
  stk_st : (VG.Proof.Poly1305.X86_64.stkR s₀).Disjoint (sR (st s₀))
  stk_d : (VG.Proof.Poly1305.X86_64.stkR s₀).Disjoint (VG.Proof.Poly1305.X86_64.dR s₀)
  stk_sc : (VG.Proof.Poly1305.X86_64.stkR s₀).Disjoint (VG.Proof.Poly1305.X86_64.scR s₀)
  nowrap : (VG.Proof.Poly1305.X86_64.dp s₀).toNat + VG.Proof.Poly1305.X86_64.dl s₀ ≤ 2 ^ 64

theorem UPre.of (s₀ : State) (h : Proof.Poly1305.updateX86_64.pre s₀) : VG.Proof.Poly1305.X86_64.UPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem dl_lt (s₀ : State) : VG.Proof.Poly1305.X86_64.dl s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt

theorem kb_lt (s₀ : State) : VG.Proof.Poly1305.X86_64.kb s₀ < 16 := Nat.mod_lt _ (by decide)

theorem rcx_eq (s₀ : State) : s₀.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀) := by simp

theorem dR_contains (s₀ : State) {i n : Nat} (h : i + n ≤ VG.Proof.Poly1305.X86_64.dl s₀) :
    (VG.Proof.Poly1305.X86_64.dR s₀).Contains (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 i) n := by
  have := VG.Proof.Poly1305.X86_64.dl_lt s₀
  exact Offset.contains_base _ h (by omega_using [h, this])

theorem UPre.st_in {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) : sR (st s₀) ∈ s₀.wr := by
  rw [hp.wr]; exact List.mem_cons_self

theorem UPre.sc_in {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) : VG.Proof.Poly1305.X86_64.scR s₀ ∈ s₀.wr := by
  rw [hp.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The accumulator and the key: what `Repr` reads. -/
abbrev rpR (st : Addr) : Region := ⟨st, 56⟩

theorem rpR_sub (st : Addr) : Region.Sub (VG.Proof.Poly1305.X86_64.rpR st) (sR st) := by
  have := Offset.sub_base st (d := 0) (n := 56) (k := 128) (by decide)
  rwa [BitVec.add_zero] at this

theorem rpR_bfR (st : Addr) : (VG.Proof.Poly1305.X86_64.rpR st).Disjoint (bfR st) := by
  simp only [bfR, off, ofInt_natCast]
  exact (Offset.disjoint_base st (d := 56) (n := 16) (k := 56) (by decide) (by decide)).symm

/-- A state represents the same message after writes outside its first 56
bytes. -/
theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.Poly1305.X86_64.rpR p).Disjoint r) {key msg : List Byte} (h : Repr m p key msg) :
    Repr m' p key msg := by
  obtain ⟨h1, h2, h3⟩ := h
  have s₁ : Region.Sub ⟨p + 24, 32⟩ (VG.Proof.Poly1305.X86_64.rpR p) := by
    have := Offset.sub_base p (d := 24) (n := 32) (k := 56) (by decide); exact this
  have s₂ : Region.Sub ⟨p, 24⟩ (VG.Proof.Poly1305.X86_64.rpR p) := by
    have := Offset.sub_base p (d := 0) (n := 24) (k := 56) (by decide)
    rwa [BitVec.add_zero] at this
  refine ⟨h1, ?_, ?_⟩
  · rw [Poly1305.bytesAt_frame hf (fun r hr => (hd r hr).sub_left s₁) (by decide), h2]
  · rw [Poly1305.bytesAt_frame hf (fun r hr => (hd r hr).sub_left s₂) (by decide), h3]

/-! ## The saved registers -/

theorem savedS_bound : ∀ q ∈ savedS, q.2 + 8 ≤ 48 := by decide

/-- The callee-saved registers of `s` are saved at `p` (in `scratch`). -/
abbrev SavedAt (p : Addr) (s : State) (m : Mem) : Prop := Spill.Saved m p s.gpr savedS

theorem SavedAt.frame {p : Addr} {s : State} {m m' : Mem} (h : VG.Proof.Poly1305.X86_64.SavedAt p s m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨p, 128⟩ : Region).Disjoint r) : VG.Proof.Poly1305.X86_64.SavedAt p s m' :=
  Spill.Saved.frame h hf fun q hq r hr =>
    (hd r hr).sub_left (Offset.sub_base p (by have := VG.Proof.Poly1305.X86_64.savedS_bound q hq; omega))

theorem saveS_ok (s : State) (hw : (⟨s.gpr .r8, 128⟩ : Region) ∈ s.wr) :
    WP isa (.block saveS) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨s.gpr .r8, 128⟩] s.mem s'.mem ∧ VG.Proof.Poly1305.X86_64.SavedAt (s.gpr .r8) s s'.mem :=
  WP.mono (Spill.save_ok .r8 savedS s fun q hq =>
      ⟨_, hw, Offset.contains_base _ (by have := VG.Proof.Poly1305.X86_64.savedS_bound q hq; omega)
        (by have := VG.Proof.Poly1305.X86_64.savedS_bound q hq; omega)⟩)
    fun s' ⟨hg, hrd, hwr, hm⟩ => ⟨hg, hrd, hwr,
      hm ▸ Spill.saveMem_frame_base _ _ _ _ (fun q hq => by have := VG.Proof.Poly1305.X86_64.savedS_bound q hq; omega) (by decide),
      hm ▸ Spill.saveMem_saved _ _ _ _ (by decide)⟩

/-! ## Invariants -/

/-- What holds from the prologue to the call. -/
structure UC (s₀ : State) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  r8 : s.gpr .r8 = VG.Proof.Poly1305.X86_64.scr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : VG.Proof.Poly1305.X86_64.SavedAt (VG.Proof.Poly1305.X86_64.scr s₀) s₀ s.mem

/-- After the prologue: only `scratch` is written. -/
structure Pre1 (s₀ : State) (s : State) : Prop extends VG.Proof.Poly1305.X86_64.UC s₀ s where
  frame : Frame [bfR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀] s₀.mem s.mem
  rsi : s.gpr .rsi = VG.Proof.Poly1305.X86_64.dp s₀
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kb s₀)
  buf : bytesAt s.mem (off (st s₀) 56) (VG.Proof.Poly1305.X86_64.kb s₀) = VG.Proof.Poly1305.X86_64.Bf s₀

/-- After copying `n` bytes of data into the buffer. -/
structure Filled (s₀ : State) (n : Nat) (s : State) : Prop extends VG.Proof.Poly1305.X86_64.UC s₀ s where
  frame : Frame [bfR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀] s₀.mem s.mem
  n_le : n ≤ VG.Proof.Poly1305.X86_64.dl s₀
  n_le' : VG.Proof.Poly1305.X86_64.kb s₀ + n ≤ 16
  rsi : s.gpr .rsi = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 n
  rcx : s.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀ - n)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kb s₀ + n)
  buf : bytesAt s.mem (off (st s₀) 56) (VG.Proof.Poly1305.X86_64.kb s₀ + n) = VG.Proof.Poly1305.X86_64.Bf s₀ ++ VG.Proof.Poly1305.X86_64.Dt s₀ n

/-- With `c` bytes of data consumed, the memory `m` represents the message
on entry followed by `X`, with `Y` buffered (`Bf ++ Dt c = X ++ Y`); `Y` is
empty unless all the data is consumed. -/
def StOk (s₀ : State) (c : Nat) (m : Mem) : Prop :=
  ∃ X Y : List Byte, X.length % 16 = 0 ∧ Y.length < 16 ∧ VG.Proof.Poly1305.X86_64.Bf s₀ ++ VG.Proof.Poly1305.X86_64.Dt s₀ c = X ++ Y ∧
    (Y = [] ∨ c = VG.Proof.Poly1305.X86_64.dl s₀) ∧ bytesAt m (off (st s₀) 56) Y.length = Y ∧
    ∀ key W, Repr s₀.mem (st s₀) key W → Repr m (st s₀) key (W ++ X)

/-- After the buffer: `c` bytes of data consumed. -/
structure AfterFill (s₀ : State) (c : Nat) (s : State) : Prop extends VG.Proof.Poly1305.X86_64.UC s₀ s where
  frame : Frame [sR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀] s₀.mem s.mem
  c_le : c ≤ VG.Proof.Poly1305.X86_64.dl s₀
  rsi : s.gpr .rsi = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c
  rcx : s.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀ - c)
  st : VG.Proof.Poly1305.X86_64.StOk s₀ c s.mem

/-- A state that differs from `s` only in the flags. -/
def FlagsOnly (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem UC.of_regs {s₀ s s' : State} (h : VG.Proof.Poly1305.X86_64.UC s₀ s)
    (hg : ∀ r ∈ [Reg.rdi, .rsp, .r8], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Poly1305.X86_64.UC s₀ s' where
  rdi := by rw [hg _ (by simp)]; exact h.rdi
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  r8 := by rw [hg _ (by simp)]; exact h.r8
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  saved := by rw [hm]; exact h.saved

theorem UC.flags {s₀ s s' : State} (h : VG.Proof.Poly1305.X86_64.UC s₀ s) (hf : VG.Proof.Poly1305.X86_64.FlagsOnly s s') : VG.Proof.Poly1305.X86_64.UC s₀ s' :=
  h.of_regs (fun r _ => by rw [hf.1]) hf.2.1 hf.2.2.1 hf.2.2.2

theorem UC.in_st {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {s : State} (h : VG.Proof.Poly1305.X86_64.UC s₀ s) : sR (s.gpr .rdi) ∈ s.wr := by
  rw [h.wr, h.rdi]; exact hp.st_in

/-- Bytes of data, read from memory written only in the state and `scratch`. -/
theorem UPre.data {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {rs : List Region} {m : Mem} (hf : Frame rs s₀.mem m)
    (hrs : ∀ r ∈ rs, Region.Sub r (sR (st s₀)) ∨ r = VG.Proof.Poly1305.X86_64.scR s₀) {i : Nat} (hi : i < VG.Proof.Poly1305.X86_64.dl s₀) :
    m (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 i) :=
  hf.bytes (R := VG.Proof.Poly1305.X86_64.dR s₀) (fun r hr => by
    rcases hrs r hr with h | rfl
    · exact hp.d_st.sub_right h
    · exact hp.d_sc) (show VG.Proof.Poly1305.X86_64.dl s₀ ≤ 2 ^ 64 by have := VG.Proof.Poly1305.X86_64.dl_lt s₀; omega_using [this]) hi

theorem bfR_sub_sR (st : Addr) : Region.Sub (bfR st) (sR st) := by
  simp only [bfR, off, ofInt_natCast]; exact Offset.sub_base st (by decide)

/-- The source of a copy from the data. -/
theorem UPre.srcOk {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {s : State} (hc : VG.Proof.Poly1305.X86_64.UC s₀ s)
    (hf : Frame [bfR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀] s₀.mem s.mem) {c n : Nat}
    (h : c + n ≤ VG.Proof.Poly1305.X86_64.dl s₀) : SrcOk s s₀.mem (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c) n := by
  intro i hi
  have e : VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 (c + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  refine ⟨⟨VG.Proof.Poly1305.X86_64.dR s₀, by rw [hc.rd, hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _),
    VG.Proof.Poly1305.X86_64.dR_contains s₀ (by omega_using [h, hi])⟩, fun hb => ?_,
    hp.data hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (VG.Proof.Poly1305.X86_64.bfR_sub_sR _)
      · exact .inr rfl) (by omega_using [h, hi])⟩
  rw [hc.rdi] at hb
  exact hp.d_st _ (VG.Proof.Poly1305.X86_64.dR_contains s₀ (by omega_using [h, hi])) (VG.Proof.Poly1305.X86_64.bfR_sub_sR _ _ hb)

/-! ## Prologue -/

set_option simprocs false in
theorem kInit_ok (s : State) :
    WP isa (.block [.mov .r12 (.reg .rsi), .alu .and .r12 (.imm 15), .mov .rsi (.reg .rdx),
      .alu .test .r12 (.reg .r12)]) s fun s' =>
      s'.gpr .r12 = BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) ∧ s'.gpr .rsi = s.gpr .rdx ∧
      s'.zf = some (BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) &&&
        BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) == 0) ∧
      Keeps [.r12, .rsi] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', and15]
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem uprologue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) :
    WP isa (.block (saveS ++ ([.mov .r12 (.reg .rsi), .alu .and .r12 (.imm 15),
      .mov .rsi (.reg .rdx), .alu .test .r12 (.reg .r12)] : List Instr))) s₀ fun s =>
      VG.Proof.Poly1305.X86_64.Pre1 s₀ s ∧ s.gpr .rcx = s₀.gpr .rcx ∧
        s.zf = some (BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kb s₀) &&& BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kb s₀) == 0) := by
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.saveS_ok s₀ hp.sc_in) fun s₁ ⟨g₁, rd₁, wr₁, f₁, sv₁⟩ => ?_)
  refine WP.mono (VG.Proof.Poly1305.X86_64.kInit_ok s₁) fun s₂ ⟨c12, csi, cz, k₂⟩ => ?_
  have g : ∀ r, r ∉ [Reg.r12, .rsi] → s₂.gpr r = s₀.gpr r := fun r hr => by rw [k₂.1 r hr, g₁]
  have hm₂ : s₂.mem = s₁.mem := k₂.2.1
  have hkb := VG.Proof.Poly1305.X86_64.kb_lt s₀
  refine ⟨⟨⟨g .rdi (by decide), g .rsp (by decide), g .r8 (by decide), by rw [k₂.2.2.1, rd₁],
    by rw [k₂.2.2.2, wr₁], by rw [hm₂]; exact sv₁⟩, ?_, by rw [csi, g₁], by rw [c12, g₁], ?_⟩,
    g .rcx (by decide), by rw [cz, g₁]⟩
  · rw [hm₂]; exact f₁.mono (by simp)
  · rw [hm₂]
    refine Poly1305.bytesAt_frame f₁ (fun r hr => ?_) (by omega_using [hkb])
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.st_sc.sub_left (sub_sR _ (by omega_using [hkb])))

/-- Nothing buffered: the state already represents the message's whole blocks. -/
theorem Pre1.after {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {s : State} (h : VG.Proof.Poly1305.X86_64.Pre1 s₀ s)
    (hrcx : s.gpr .rcx = s₀.gpr .rcx) (hk : VG.Proof.Poly1305.X86_64.kb s₀ = 0) : VG.Proof.Poly1305.X86_64.AfterFill s₀ 0 s :=
  { h.toUC with
    frame := h.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, VG.Proof.Poly1305.X86_64.bfR_sub_sR _⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    c_le := Nat.zero_le _
    rsi := by rw [h.rsi]; simp
    rcx := by rw [hrcx]; simp
    st := ⟨[], [], rfl, by decide, by simp only [VG.Proof.Poly1305.X86_64.Bf, VG.Proof.Poly1305.X86_64.Dt, hk]; rfl, .inl rfl, rfl,
      fun key W hr => by
        rw [List.append_nil]
        refine VG.Proof.Poly1305.X86_64.repr_frame h.frame (fun r hr' => ?_) hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · exact VG.Proof.Poly1305.X86_64.rpR_bfR _
        · exact hp.st_sc.sub_left (VG.Proof.Poly1305.X86_64.rpR_sub _)⟩ }

/-! ## Filling the buffer -/

/-- `Pre1` is kept by changes to `rax`, `rcx` and the flags. -/
theorem Pre1.of_regs {s₀ s s' : State} (h : VG.Proof.Poly1305.X86_64.Pre1 s₀ s) (hg : ∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Poly1305.X86_64.Pre1 s₀ s' :=
  { h.toUC.of_regs (fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) hm hrd hwr with
    frame := by rw [hm]; exact h.frame
    rsi := by rw [hg _ (by decide) (by decide)]; exact h.rsi
    r12 := by rw [hg _ (by decide) (by decide)]; exact h.r12
    buf := by rw [hm]; exact h.buf }

/-- The number of bytes to copy, `n = min(16 - kb, dl)`, into `rax`, and
`dl - n` into `rcx`. -/
theorem count_ok {s₀ : State} {s : State} (h : VG.Proof.Poly1305.X86_64.Pre1 s₀ s) (hrcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa count s fun s' =>
      VG.Proof.Poly1305.X86_64.Pre1 s₀ s' ∧ s'.gpr .rax = BitVec.ofNat 64 (min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀)) ∧
        s'.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀ - min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀)) ∧
        s'.zf = some (decide (min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀) = 0)) := by
  have hkl := VG.Proof.Poly1305.X86_64.kb_lt s₀
  have hdl := VG.Proof.Poly1305.X86_64.dl_lt s₀
  have e16 : BitVec.setWidth 64 (16 : BitVec 32) - BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kb s₀) =
      BitVec.ofNat 64 (16 - VG.Proof.Poly1305.X86_64.kb s₀) := by
    rw [show BitVec.setWidth 64 (16 : BitVec 32) = BitVec.ofNat 64 16 by decide, sub_ofNat (by omega_using [hkl])]
  refine WP.seq (wp_mov32i fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_cmp fun s₃ g₃ m₃ rd₃ wr₃ cf₃ _ =>
    WP.block_nil ?_)
  have hrax₂ : s₂.gpr .rax = BitVec.ofNat 64 (16 - VG.Proof.Poly1305.X86_64.kb s₀) := by
    rw [u₂.gpr, u₁.other .r12 (by decide), h.r12, u₁.gpr, e16]
  have hrcx₂ : s₂.gpr .rcx = s₀.gpr .rcx := by
    rw [u₂.other .rcx (by decide), u₁.other .rcx (by decide), hrcx]
  have hrax₃ : s₃.gpr .rax = BitVec.ofNat 64 (16 - VG.Proof.Poly1305.X86_64.kb s₀) := by rw [g₃, hrax₂]
  have hrcx₃ : s₃.gpr .rcx = s₀.gpr .rcx := by rw [g₃, hrcx₂]
  have hP₃ : VG.Proof.Poly1305.X86_64.Pre1 s₀ s₃ := h.of_regs (fun r h1 _ => by rw [g₃, u₂.other r h1, u₁.other r h1])
    (by rw [m₃, u₂.mem, u₁.mem]) (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
  -- `rax = n`.
  refine WP.seq (WP.mono (Q := fun s₄ : State => VG.Proof.Poly1305.X86_64.Pre1 s₀ s₄ ∧ s₄.gpr .rcx = s₀.gpr .rcx ∧
      s₄.gpr .rax = BitVec.ofNat 64 (min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀))) ?_ fun s₄ ⟨hP₄, hrcx₄, hrax₄⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.Poly1305.X86_64.dl s₀ < 16 - VG.Proof.Poly1305.X86_64.kb s₀)) (by
      simp only [eval, cf₃, hrcx₂, hrax₂, toNat_ofNat_lt (show 16 - VG.Proof.Poly1305.X86_64.kb s₀ < 2 ^ 64 by omega_using [hkl])])
      (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov fun s₄ u₄ => WP.block_nil ⟨hP₃.of_regs (fun r h1 _ => u₄.other r h1) u₄.mem u₄.rd u₄.wr,
        by rw [u₄.other _ (by decide), hrcx₃], ?_⟩
      simp only [decide_eq_true_eq] at hb
      rw [u₄.gpr, hrcx₃, Nat.min_eq_right (by omega_using [hb]), VG.Proof.Poly1305.X86_64.rcx_eq]
    · refine WP.block_nil ⟨hP₃, hrcx₃, ?_⟩
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      rw [hrax₃, Nat.min_eq_left hb]
  · refine wp_sub fun s₅ u₅ => wp_test fun s₆ g₆ m₆ rd₆ wr₆ z₆ => WP.block_nil ?_
    have hg : ∀ r, r ≠ .rcx → s₆.gpr r = s₄.gpr r := fun r hr => by rw [g₆, u₅.other r hr]
    refine ⟨hP₄.of_regs (fun r _ h2 => hg r h2) (by rw [m₆, u₅.mem]) (by rw [rd₆, u₅.rd])
      (by rw [wr₆, u₅.wr]), by rw [hg _ (by decide)]; exact hrax₄, ?_, ?_⟩
    · rw [g₆, u₅.gpr, hrcx₄, hrax₄, VG.Proof.Poly1305.X86_64.rcx_eq, sub_ofNat (by omega_using [])]
    · rw [z₆, u₅.other _ (by decide), hrax₄, BitVec.and_self, ofNat_beq_zero (by omega_using [hdl])]

theorem copyFill_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {s : State} (h : VG.Proof.Poly1305.X86_64.Pre1 s₀ s) {n : Nat} (hn : n ≤ VG.Proof.Poly1305.X86_64.dl s₀)
    (hn' : VG.Proof.Poly1305.X86_64.kb s₀ + n ≤ 16) (hrax : s.gpr .rax = BitVec.ofNat 64 n)
    (hrcx : s.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀ - n)) (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) copyIn) s (VG.Proof.Poly1305.X86_64.Filled s₀ n) := by
  refine WP.ite (decide (n = 0)) (by simp [eval, hz]) (fun h0 => ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0
    subst h0
    exact WP.block_nil { h.toUC with
      frame := h.frame, n_le := hn, n_le' := hn', rsi := by rw [h.rsi]; simp, rcx := hrcx,
      r12 := by rw [h.r12]; simp
      buf := by rw [Nat.add_zero, h.buf]; simp [VG.Proof.Poly1305.X86_64.Dt, bytesAt] }
  · simp only [decide_eq_false_iff_not] at h0
    have hsrc := hp.srcOk h.toUC h.frame (c := 0) (n := n) (by omega_using [hn])
    refine WP.mono (copy_ok (j0 := VG.Proof.Poly1305.X86_64.kb s₀) (by omega_using [hn']) (by omega_using [h0]) (h.toUC.in_st hp)
      hsrc (by rw [h.rsi]; simp) (by rw [h.r12]) hrax) fun s' hc => ?_
    have hk : ∀ r ∈ [Reg.rdi, .rsp, .r8], s'.gpr r = s.gpr r := fun r hr => hc.keep r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)
    have hf : Frame [bfR (st s₀)] s.mem s'.mem := by rw [← h.rdi]; exact hc.frame (by omega_using [hn'])
    refine { rdi := by rw [hk _ (by simp)]; exact h.rdi
             rsp := by rw [hk _ (by simp)]; exact h.rsp
             r8 := by rw [hk _ (by simp)]; exact h.r8
             rd := hc.rd.trans h.rd
             wr := hc.wr.trans h.wr
             saved := h.saved.frame hf (fun r hr => by
               simp only [List.mem_singleton] at hr; subst hr
               exact hp.st_sc.symm.sub_right (VG.Proof.Poly1305.X86_64.bfR_sub_sR _))
             frame := h.frame.trans (hf.mono (by simp))
             n_le := hn, n_le' := hn', rsi := by rw [hc.rsi]; simp
             rcx := by rw [hc.keep _ (by decide) (by decide) (by decide) (by decide), hrcx]
             r12 := hc.r12
             buf := ?_ }
    have hb := hc.buf (by omega_using [hn'])
    rw [h.rdi, h.buf] at hb
    rw [hb]
    simp [VG.Proof.Poly1305.X86_64.Dt]

/-! ## Absorbing the full buffer -/

/-- The memory after keeping `a, b, c` in the state's working space. -/
def stash (m : Mem) (st : Addr) (a b c : BitVec 64) : Mem :=
  ((m.writeW (off st 72) a).writeW (off st 80) b).writeW (off st 88) c

set_option simprocs false in
theorem stash_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block [.store (at_ .rdi 72) .rsi, .store (at_ .rdi 80) .rcx, .store (at_ .rdi 88) .r8]) s
      fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = VG.Proof.Poly1305.X86_64.stash s.mem (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r8) := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 72 (by decide); have o1 := o 80 (by decide); have o2 := o 88 (by decide)
  simp only [off] at o0 o1 o2
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    State.store64, o0, o1, o2, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, rfl⟩

theorem stash_frame (m : Mem) (st : Addr) (a b c : BitVec 64) : Frame [wR st] m (VG.Proof.Poly1305.X86_64.stash m st a b c) := by
  have k : ∀ d, 56 ≤ d → d + 8 ≤ 128 → (wR st).Contains (off st d) (64 / 8) :=
    fun d h₁ h₂ => wR_contains st h₁ h₂
  exact (((Frame.refl _ _).writeW List.mem_cons_self _ (k 72 (by decide) (by decide))).writeW
    List.mem_cons_self _ (k 80 (by decide) (by decide))).writeW List.mem_cons_self _ (k 88 (by decide) (by decide))

theorem stash_low (m : Mem) (st : Addr) (a b c : BitVec 64) {d : Nat} (hd : d + 8 ≤ 72) :
    (VG.Proof.Poly1305.X86_64.stash m st a b c).readW (off st d) 64 = m.readW (off st d) 64 := by
  simp only [VG.Proof.Poly1305.X86_64.stash]
  rw [readW_writeW_off _ _ _ (by omega_using [hd]) (by decide) (by omega_using [hd]),
    readW_writeW_off _ _ _ (by omega_using [hd]) (by decide) (by omega_using [hd]),
    readW_writeW_off _ _ _ (by omega_using [hd]) (by decide) (by omega_using [hd])]

/-- The buffer is not where `stash` writes. -/
theorem stash_buf (m : Mem) (st : Addr) (a b c : BitVec 64) :
    bytesAt (VG.Proof.Poly1305.X86_64.stash m st a b c) (off st 56) 16 = bytesAt m (off st 56) 16 := by
  have f : Frame [⟨off st 72, 24⟩] m (VG.Proof.Poly1305.X86_64.stash m st a b c) := by
    have k : ∀ d, 72 ≤ d → d + 8 ≤ 96 → (⟨off st 72, 24⟩ : Region).Contains (off st d) (64 / 8) := by
      intro d h₁ h₂
      simp only [off, ofInt_natCast]; exact Offset.contains st h₁ (by omega_using [h₂]) (by decide)
    exact (((Frame.refl _ _).writeW List.mem_cons_self _ (k 72 (by decide) (by decide))).writeW
      List.mem_cons_self _ (k 80 (by decide) (by decide))).writeW List.mem_cons_self _
      (k 88 (by decide) (by decide))
  refine Poly1305.bytesAt_frame f (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  simp only [off, ofInt_natCast]
  exact Offset.disjoint st (by decide) (by decide) (by decide)

set_option simprocs false in
/-- Storing `h` and loading back `rsi`, `rcx` and `r8`. -/
theorem storeReload_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block [.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx, .store (at_ .rdi 16) .rbp,
      .mov .rsi (.mem (at_ .rdi 72)), .mov .rcx (.mem (at_ .rdi 80)), .mov .r8 (.mem (at_ .rdi 88))]) s
      fun s' =>
      s'.mem = storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp) ∧
      s'.gpr .rsi = (storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)).readW
        (off (s.gpr .rdi) 72) 64 ∧
      s'.gpr .rcx = (storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)).readW
        (off (s.gpr .rdi) 80) 64 ∧
      s'.gpr .r8 = (storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)).readW
        (off (s.gpr .rdi) 88) 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, contains_off hd (by omega_using [hd])⟩
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_off hd (by omega_using [hd])⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  have i0 := i 72 (by decide); have i1 := i 80 (by decide); have i2 := i 88 (by decide)
  simp only [off] at o0 o8 o16 i0 i1 i2
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, State.store64, State.load64, State.setReg, o0, o8, o16, i0, i1, i2,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, fun r h1 h2 h3 => ?_, ?_⟩
  · simp only [h1, h2, h3, ite_false]
  · trivial

theorem absorbBuf_eq : absorbBuf =
    ([.store (at_ .rdi 72) .rsi, .store (at_ .rdi 80) .rcx, .store (at_ .rdi 88) .r8] : List Instr) ++
    (setup ++ (absorbAt .rdi 56 1 ++ (reduce ++
    ([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx, .store (at_ .rdi 16) .rbp,
      .mov .rsi (.mem (at_ .rdi 72)), .mov .rcx (.mem (at_ .rdi 80)), .mov .r8 (.mem (at_ .rdi 88))] :
      List Instr)))) := by
  simp only [absorbBuf, List.append_assoc, List.cons_append, List.nil_append]

theorem off_disj_bfR (st : Addr) {d : Nat} (hd : d + 8 ≤ 56) :
    (⟨off st d, 8⟩ : Region).Disjoint (bfR st) := by
  simp only [bfR, off, ofInt_natCast]
  exact Offset.disjoint st (by omega_using [hd]) (by omega_using [hd]) (by decide)

/-- A word of the accumulator or the key, unchanged since entry. -/
theorem Filled.low {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {n : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.Filled s₀ n s) {d : Nat}
    (hd : d + 8 ≤ 56) : s.mem.readW (off (st s₀) d) 64 = s₀.mem.readW (off (st s₀) d) 64 := by
  refine h.frame.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.Poly1305.X86_64.off_disj_bfR _ hd
  · exact hp.st_sc.sub_left (sub_sR _ (by omega_using [hd]))

theorem hR_sub_sR (st : Addr) : Region.Sub (hR st) (sR st) := by
  have := sub_sR st (d := 0) (n := 24) (by decide)
  rwa [off_eq, BitVec.add_zero] at this

theorem wR_sub_sR (st : Addr) : Region.Sub (wR st) (sR st) := sub_sR st (d := 56) (n := 72) (by decide)

theorem hR_wR_sub (st : Addr) (R : Region) :
    ∀ r ∈ [hR st, wR st], ∃ r' ∈ [sR st, R], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  refine ⟨sR st, List.mem_cons_self, ?_⟩
  rcases hr with rfl | rfl
  · exact VG.Proof.Poly1305.X86_64.hR_sub_sR st
  · exact VG.Proof.Poly1305.X86_64.wR_sub_sR st

theorem bfR_sc_sub (st : Addr) (R : Region) :
    ∀ r ∈ [bfR st, R], ∃ r' ∈ [sR st, R], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, VG.Proof.Poly1305.X86_64.bfR_sub_sR _⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-- Absorbing the full buffer. -/
theorem absorbFull_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {s : State} {n : Nat} (h : VG.Proof.Poly1305.X86_64.Filled s₀ n s)
    (hfull : VG.Proof.Poly1305.X86_64.kb s₀ + n = 16) : WP isa (.block absorbBuf) s (VG.Proof.Poly1305.X86_64.AfterFill s₀ n) := by
  have hq : (R1 s₀).toNat % 4 = 0 := r1_mod _
  have hq' : (R1 s₀).toNat < 2 ^ 60 := r1_lt _
  have hw : sR (s.gpr .rdi) ∈ s.wr := h.toUC.in_st hp
  rw [VG.Proof.Poly1305.X86_64.absorbBuf_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.stash_ok s hw) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_)
  have hw₁ : sR (s₁.gpr .rdi) ∈ s₁.wr := by rw [g₁, wr₁]; exact hw
  refine WP.block_append (WP.mono (setup_ok s₁ (List.mem_append_right _ hw₁))
    fun s₂ ⟨e8, e9, e10, e11, e12, e13, k₂⟩ => ?_)
  have low : ∀ d, d + 8 ≤ 56 →
      s₁.mem.readW (off (s₁.gpr .rdi) d) 64 = s₀.mem.readW (off (st s₀) d) 64 := by
    intro d hd
    rw [m₁, g₁, h.rdi, VG.Proof.Poly1305.X86_64.stash_low _ _ _ _ _ (by omega_using [hd]), h.low hp hd]
  rw [low 24 (by decide)] at e8
  rw [low 32 (by decide)] at e9
  replace e8 : s₂.gpr .r8 = R0 s₀ := e8
  replace e9 : s₂.gpr .r9 = R1 s₀ := e9
  rw [low 0 (by decide)] at e11
  rw [low 8 (by decide)] at e12
  rw [low 16 (by decide)] at e13
  have rdi₂ : s₂.gpr .rdi = st s₀ := by rw [k₂.gpr' (r := .rdi), g₁, h.rdi]
  have hw₂ : sR (s₂.gpr .rdi) ∈ s₂.wr := by rw [k₂.2.2.2, k₂.gpr' (r := .rdi)]; exact hw₁
  refine WP.block_append (WP.mono (absorbBuf_ok s₂ (pad := 1) (Or.inr rfl) hw₂ (q := (R1 s₀).toNat / 4)
    (by rw [e8]; exact r0_lt _) (by rw [e9]; omega_using [hq]) (by omega_using [hq, hq'])
    (by rw [e10, e9])) fun s₃ ⟨ha, k₃⟩ => ?_)
  have rdi₃ : s₃.gpr .rdi = st s₀ := by rw [k₃.gpr' (r := .rdi), rdi₂]
  refine WP.block_append (WP.mono (reduce_ok s₃) fun s₄ ⟨hr, k₄⟩ => ?_)
  have rdi₄ : s₄.gpr .rdi = st s₀ := by rw [k₄.gpr' (r := .rdi), rdi₃]
  have hw₄ : sR (s₄.gpr .rdi) ∈ s₄.wr := by rw [k₄.2.2.2, k₃.2.2.2, rdi₄, ← rdi₂]; exact hw₂
  refine WP.mono (VG.Proof.Poly1305.X86_64.storeReload_ok s₄ hw₄) fun s₅ ⟨m₅, rsi₅, rcx₅, r8₅, g₅, rd₅, wr₅⟩ => ?_
  have mem₄ : s₄.mem = VG.Proof.Poly1305.X86_64.stash s.mem (st s₀) (s.gpr .rsi) (s.gpr .rcx) (s.gpr .r8) := by
    rw [k₄.2.1, k₃.2.1, k₂.2.1, m₁, h.rdi]
  rw [rdi₄, mem₄] at m₅ rsi₅ rcx₅ r8₅
  rw [storeH_saved _ _ _ _ _ (by decide) (by decide)] at rsi₅ rcx₅ r8₅
  simp only [VG.Proof.Poly1305.X86_64.stash] at rsi₅ rcx₅ r8₅
  rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide),
    readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64] at rsi₅
  rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64] at rcx₅
  rw [Mem.readW_writeW_self64] at r8₅
  -- Registers.
  have rdi₅ : s₅.gpr .rdi = st s₀ := by rw [g₅ _ (by decide) (by decide) (by decide), rdi₄]
  have rsp₅ : s₅.gpr .rsp = s₀.gpr .rsp := by
    rw [g₅ _ (by decide) (by decide) (by decide), k₄.gpr' (r := .rsp), k₃.gpr' (r := .rsp),
      k₂.gpr' (r := .rsp), g₁, h.rsp]
  -- Memory.
  have fs : Frame [hR (st s₀), wR (st s₀)] s.mem s₅.mem := by
    rw [m₅]; exact storeH_frame ((VG.Proof.Poly1305.X86_64.stash_frame _ _ _ _ _).mono (by simp)) _ _ _
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, rd₁, h.rd]
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, wr₁, h.wr]
  have hf₅ : Frame [sR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀] s₀.mem s₅.mem :=
    (h.frame.sub (VG.Proof.Poly1305.X86_64.bfR_sc_sub _ _)).trans (fs.sub (VG.Proof.Poly1305.X86_64.hR_wR_sub _ _))
  have hl : (VG.Proof.Poly1305.X86_64.Bf s₀ ++ VG.Proof.Poly1305.X86_64.Dt s₀ n).length = 16 := by
    simp only [List.length_append, VG.Proof.Poly1305.X86_64.Dt, Poly1305.length_bytesAt]; omega_using [hfull]
  refine { rdi := rdi₅, rsp := rsp₅, r8 := by rw [r8₅]; exact h.r8, rd := rd₅', wr := wr₅'
           saved := h.saved.frame fs (fun r hr => by
             obtain ⟨r', hr', hs⟩ := VG.Proof.Poly1305.X86_64.hR_wR_sub (st s₀) (VG.Proof.Poly1305.X86_64.scR s₀) r hr
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
             rcases hr' with rfl | rfl
             · exact hp.st_sc.symm.sub_right hs
             · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
               rcases hr with rfl | rfl
               · exact hp.st_sc.symm.sub_right (VG.Proof.Poly1305.X86_64.hR_sub_sR _)
               · exact hp.st_sc.symm.sub_right (VG.Proof.Poly1305.X86_64.wR_sub_sR _))
           frame := hf₅
           c_le := h.n_le
           rsi := by rw [rsi₅]; exact h.rsi
           rcx := by rw [rcx₅]; exact h.rcx
           st := ⟨VG.Proof.Poly1305.X86_64.Bf s₀ ++ VG.Proof.Poly1305.X86_64.Dt s₀ n, [], by omega_using [hl], by decide, (List.append_nil _).symm, .inl rfl,
             rfl, fun key W hrep => ?_⟩ }
  -- The accumulator.
  obtain ⟨hlen, hkey, hacc⟩ := hrep
  have hH2 := H2_le ⟨hlen, hkey, hacc⟩
  have hb₂ : (s₂.gpr .rbp).toNat ≤ 4 := by rw [e13]; exact hH2
  obtain ⟨hv₃, hb₃⟩ := ha hb₂
  have hR4 := hr hb₃
  have hbuf : bytesAt s₂.mem (off (s₂.gpr .rdi) 56) 16 = VG.Proof.Poly1305.X86_64.Bf s₀ ++ VG.Proof.Poly1305.X86_64.Dt s₀ n := by
    rw [k₂.2.1, m₁, rdi₂, h.rdi, VG.Proof.Poly1305.X86_64.stash_buf, ← hfull, h.buf]
  have hkey₀ : bytesAt s₀.mem (off (st s₀) 24) 32 = key := by rw [off_24]; exact hkey
  have hkey₅ : bytesAt s₅.mem (off (st s₀) 24) 32 = key := by
    rw [← hkey₀, key_frame fs]
    refine Poly1305.bytesAt_frame h.frame (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (kR_disjoint _ _ (List.mem_cons_of_mem _ List.mem_cons_self)).sub_right (bfR_sub_wR _)
    · exact hp.st_sc.sub_left (sub_sR _ (by decide))
  have hA : accumulate (Rn s₀) W = A0 s₀ := by rw [A0, hacc, ← hkey₀, clamp_key]
  have e : leNum (VG.Proof.Poly1305.X86_64.Bf s₀ ++ VG.Proof.Poly1305.X86_64.Dt s₀ n ++ [0x01]) = leNum (VG.Proof.Poly1305.X86_64.Bf s₀ ++ VG.Proof.Poly1305.X86_64.Dt s₀ n) + 2 ^ 128 * 1 := by
    rw [Poly1305.leNum_append, hl]; rfl
  have h2 : hval s₂ = A0 s₀ := by simp only [hval, e11, e12, e13]; rw [A0, leNum_acc]
  refine ⟨by rw [List.length_append]; omega_using [hlen, hl], by rw [← off_24]; exact hkey₅, ?_⟩
  rw [m₅, storeH_acc, ← hkey₀, clamp_key, Poly1305.accumulate_append hlen, hA,
    Poly1305.absorbAll_block (by rw [hl]; decide) (by rw [hl]), e]
  change hval s₄ = _
  rw [hR4, hv₃, hbuf, h2, e8, e9, show (1 : BitVec 32).toNat = 1 from rfl, mod_step (X := A0 s₀) rfl,
    Nat.mod_mod]

theorem Filled.flags {s₀ s s' : State} {n : Nat} (h : VG.Proof.Poly1305.X86_64.Filled s₀ n s) (hf : VG.Proof.Poly1305.X86_64.FlagsOnly s s') :
    VG.Proof.Poly1305.X86_64.Filled s₀ n s' :=
  { h.toUC.flags hf with
    frame := by rw [hf.2.1]; exact h.frame
    n_le := h.n_le, n_le' := h.n_le', rsi := by rw [hf.1]; exact h.rsi, rcx := by rw [hf.1]; exact h.rcx,
    r12 := by rw [hf.1]; exact h.r12, buf := by rw [hf.2.1]; exact h.buf }

/-- `min(16 - kb, dl)` bytes into the buffer, which is absorbed if that fills it. -/
theorem fill_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {s : State} (h : VG.Proof.Poly1305.X86_64.Pre1 s₀ s) (hrcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa fill s fun s' => ∃ c, VG.Proof.Poly1305.X86_64.AfterFill s₀ c s' := by
  have hkl := VG.Proof.Poly1305.X86_64.kb_lt s₀
  have hdl := VG.Proof.Poly1305.X86_64.dl_lt s₀
  have hn : min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀) ≤ VG.Proof.Poly1305.X86_64.dl s₀ := Nat.min_le_right _ _
  have hn' : VG.Proof.Poly1305.X86_64.kb s₀ + min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀) ≤ 16 := by
    have := Nat.min_le_left (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀); omega_using [hkl, this]
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.count_ok h hrcx) fun s₁ ⟨h₁, hrax₁, hrcx₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.copyFill_ok hp h₁ hn hn' hrax₁ hrcx₁ hz₁) fun s₂ h₂ => ?_)
  refine WP.seq (wp_cmpi fun s₃ g₃ m₃ rd₃ wr₃ _ z₃ => WP.block_nil ?_)
  have hf : VG.Proof.Poly1305.X86_64.FlagsOnly s₂ s₃ := ⟨g₃, m₃, rd₃, wr₃⟩
  have h₃ := h₂.flags hf
  refine WP.ite (decide (VG.Proof.Poly1305.X86_64.kb s₀ + min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀) = 16))
    (by simp only [eval, z₃, h₂.r12, se16']
        rw [sub_beq (a := VG.Proof.Poly1305.X86_64.kb s₀ + min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀)) (b := 16) (by omega_using [hn']) (by decide)])
    (fun hfull => ?_) (fun hnf => ?_)
  · exact WP.mono (VG.Proof.Poly1305.X86_64.absorbFull_ok hp h₃ (by simpa using hfull)) fun s' h' => ⟨_, h'⟩
  · simp only [decide_eq_false_iff_not] at hnf
    have hnd : min (16 - VG.Proof.Poly1305.X86_64.kb s₀) (VG.Proof.Poly1305.X86_64.dl s₀) = VG.Proof.Poly1305.X86_64.dl s₀ := by omega_using [hkl, hn, hn', hnf]
    refine WP.block_nil ⟨VG.Proof.Poly1305.X86_64.dl s₀, { h₃.toUC with
      frame := h₃.frame.sub (VG.Proof.Poly1305.X86_64.bfR_sc_sub _ _)
      c_le := Nat.le_refl _
      rsi := by rw [h₃.rsi, hnd]
      rcx := by rw [h₃.rcx, hnd]
      st := ⟨[], VG.Proof.Poly1305.X86_64.Bf s₀ ++ VG.Proof.Poly1305.X86_64.Dt s₀ (VG.Proof.Poly1305.X86_64.dl s₀), rfl, ?_, rfl, .inr rfl, ?_, fun key W hr => ?_⟩ }⟩
    · simp only [List.length_append, VG.Proof.Poly1305.X86_64.Dt, Poly1305.length_bytesAt]; omega_using [hn', hnf, hnd]
    · have hb := h₃.buf
      rw [hnd] at hb
      simp only [List.length_append, VG.Proof.Poly1305.X86_64.Dt, Poly1305.length_bytesAt]
      exact hb
    · rw [List.append_nil]
      refine VG.Proof.Poly1305.X86_64.repr_frame h₃.frame (fun r hr' => ?_) hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact VG.Proof.Poly1305.X86_64.rpR_bfR _
      · exact hp.st_sc.sub_left (VG.Proof.Poly1305.X86_64.rpR_sub _)

/-! ## The arguments of the call -/

theorem wp_shr4 {is : List Instr} {s : State} {Q : State → Prop} {d : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d >>> 4) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d 4 :: is)) s Q :=
  WP.cons rfl (k _ (Upd.withFlags _ _ _ _ _ _ _))

theorem shr4_ofNat {len : Nat} (h : len < 2 ^ 64) :
    BitVec.ofNat 64 len >>> 4 = BitVec.ofNat 64 (len / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt h, toNat_ofNat_lt (by omega_using [h]),
    Nat.shiftRight_eq_div_pow]

/-- Before the call, or none: `c` bytes of data consumed, and what is kept across it. -/
structure Ready (s₀ : State) (c : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rbx : s.gpr .rbx = st s₀
  rsi : s.gpr .rsi = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c
  rbp : s.gpr .rbp = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀ - c)
  rdx : s.gpr .rdx = BitVec.ofNat 64 ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16)
  r15 : s.gpr .r15 = VG.Proof.Poly1305.X86_64.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀] s₀.mem s.mem
  saved : VG.Proof.Poly1305.X86_64.SavedAt (VG.Proof.Poly1305.X86_64.scr s₀) s₀ s.mem
  c_le : c ≤ VG.Proof.Poly1305.X86_64.dl s₀
  cf : s.cf = some (decide (VG.Proof.Poly1305.X86_64.dl s₀ - c < 16))
  st : VG.Proof.Poly1305.X86_64.StOk s₀ c s.mem

theorem callArgs_ok {s₀ : State} {c : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.AfterFill s₀ c s) :
    WP isa (.block callArgs) s (VG.Proof.Poly1305.X86_64.Ready s₀ c) := by
  have hdl := VG.Proof.Poly1305.X86_64.dl_lt s₀
  unfold callArgs
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => VG.Proof.Poly1305.X86_64.wp_shr4 fun s₆ u₆ => wp_cmpi fun s₇ g₇ m₇ rd₇ wr₇ cf₇ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .rdx → s₇.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [g₇, u₆.other r h5, u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have rcx₅ : s₅.gpr .rcx = s.gpr .rcx := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  have mem₇ : s₇.mem = s.mem := by rw [m₇, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  exact {
    rdi := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.rdi
    rbx := by
      rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]; exact h.rdi
    rsi := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.rsi
    rbp := by
      rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact h.rsi
    r12 := by
      rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]; exact h.rcx
    rdx := by
      rw [g₇, u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h.rcx, VG.Proof.Poly1305.X86_64.shr4_ofNat (by omega_using [hdl])]
    r15 := by rw [g₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; exact h.r8
    rsp := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.rsp
    rd := by rw [rd₇, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact h.rd
    wr := by rw [wr₇, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr
    frame := by rw [mem₇]; exact h.frame
    saved := by rw [mem₇]; exact h.saved
    c_le := h.c_le
    cf := by
      rw [cf₇, u₆.other _ (by decide), rcx₅, h.rcx, se16', toNat_ofNat_lt (by omega_using [hdl]),
        toNat_ofNat_lt (by decide)]
    st := by rw [mem₇]; exact h.st }

theorem updatePre_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) :
    WP isa updatePre s₀ fun s => ∃ c, VG.Proof.Poly1305.X86_64.Ready s₀ c s := by
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.uprologue_ok hp) fun s₁ ⟨h₁, hrcx, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ c, VG.Proof.Poly1305.X86_64.AfterFill s₀ c s) ?_ fun s₂ ⟨c, h₂⟩ =>
    WP.mono (VG.Proof.Poly1305.X86_64.callArgs_ok h₂) fun s₃ h₃ => ⟨c, h₃⟩)
  refine WP.ite (BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kb s₀) &&& BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kb s₀) == 0) (by simp [eval, hz])
    (fun h => ?_) (fun _ => VG.Proof.Poly1305.X86_64.fill_ok hp h₁ hrcx)
  rw [BitVec.and_self, ofNat_beq_zero (by have := VG.Proof.Poly1305.X86_64.kb_lt s₀; omega_using [this])] at h
  simp only [decide_eq_true_eq] at h
  exact WP.block_nil ⟨0, h₁.after hp hrcx h⟩

end VG.Proof.Poly1305.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.UpdateCall`. -/
section

/-!
# Poly1305 on x86-64: `update`, from the call on

The call of an implementation of `vg_poly1305_blocks` for the whole blocks of
the data (`BlocksImpl`), copying the rest into the buffer, restoring the
registers, and the whole function.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The call -/

/-- After the call, or none: what is kept across it, and the whole blocks of
the data absorbed. -/
structure After (s₀ : State) (c : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀ - c)
  r15 : s.gpr .r15 = VG.Proof.Poly1305.X86_64.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀, VG.Proof.Poly1305.X86_64.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.Poly1305.X86_64.SavedAt (VG.Proof.Poly1305.X86_64.scr s₀) s₀ s.mem
  c_le : c ≤ VG.Proof.Poly1305.X86_64.dl s₀
  st : VG.Proof.Poly1305.X86_64.StOk s₀ (c + 16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16)) s.mem

/-- No whole blocks: nothing to call. -/
theorem Ready.after {s₀ : State} {c : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.Ready s₀ c s) (hlt : VG.Proof.Poly1305.X86_64.dl s₀ - c < 16) :
    VG.Proof.Poly1305.X86_64.After s₀ c s where
  rbx := h.rbx
  rbp := h.rbp
  r12 := h.r12
  r15 := h.r15
  rsp := h.rsp
  rd := h.rd
  wr := h.wr
  frame := h.frame.mono (by simp)
  saved := h.saved
  c_le := h.c_le
  st := by rw [Nat.div_eq_of_lt hlt, Nat.mul_zero, Nat.add_zero]; exact h.st

/-- The return address a call stores. -/
theorem callEntry_frame (s : State) : Frame [below (s.gpr .rsp) 8] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- Data from byte `a`. -/
theorem dsub (s₀ : State) {a n : Nat} (h : a + n ≤ VG.Proof.Poly1305.X86_64.dl s₀) :
    Region.Sub ⟨VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 a, n⟩ (VG.Proof.Poly1305.X86_64.dR s₀) := Offset.sub_base _ h

/-- The stack the callee uses: its return address, and up to 16 bytes below. -/
theorem callee_stk (sp : Addr) {k : Nat} (hk : k ≤ 16) : Region.Sub (below (sp - 8) k) (below sp 24) :=
  fun x hx => below_sub (by omega_using [hk]) (by decide) x (below_callee sp k x hx)

theorem ret8_stk (sp : Addr) : Region.Sub (below sp 8) (below sp 24) := below_sub (by decide) (by decide)

/-- The blocks the call absorbs. -/
abbrev blkR (s₀ : State) (c : Nat) : Region := ⟨VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c, 16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16)⟩

theorem blk_toNat (s₀ : State) (c : Nat) :
    (BitVec.ofNat 64 ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16)).toNat = (VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16 := by
  have := VG.Proof.Poly1305.X86_64.dl_lt s₀
  exact toNat_ofNat_lt (by omega_using [this])

theorem blk_le {s₀ : State} {c : Nat} (h : c ≤ VG.Proof.Poly1305.X86_64.dl s₀) : c + 16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16) ≤ VG.Proof.Poly1305.X86_64.dl s₀ := by
  have := Nat.mul_div_le (VG.Proof.Poly1305.X86_64.dl s₀ - c) 16; omega_using [this, h]

theorem blk_dR {s₀ : State} {c : Nat} (h : c ≤ VG.Proof.Poly1305.X86_64.dl s₀) : Region.Sub (VG.Proof.Poly1305.X86_64.blkR s₀ c) (VG.Proof.Poly1305.X86_64.dR s₀) :=
  VG.Proof.Poly1305.X86_64.dsub s₀ (VG.Proof.Poly1305.X86_64.blk_le h)

section
variable (v : BlocksImpl) {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {c : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.Ready s₀ c s)
include hp h

/-- The callee's precondition, with the regions it is given, and that it is given
regions we have. -/
theorem call_pre :
    (blocksStack v.stack).pre (s.callEntry.withRegions [VG.Proof.Poly1305.X86_64.blkR s₀ c] [sR (st s₀)]) ∧
    Covers ([VG.Proof.Poly1305.X86_64.blkR s₀ c] ++ [sR (st s₀)]) (s.rd ++ s.wr) ∧ Covers [sR (st s₀)] s.wr := by
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.rsp
  have hstk : Region.Sub (below (s.gpr .rsp) 24) (VG.Proof.Poly1305.X86_64.stkR s₀) := by rw [hsp]; exact fun _ h => h
  have hle := VG.Proof.Poly1305.X86_64.blk_le h.c_le
  have hdl := VG.Proof.Poly1305.X86_64.dl_lt s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [blocksStack, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      h.rdi, h.rsi, h.rdx, VG.Proof.Poly1305.X86_64.blk_toNat]
    refine ⟨trivial, trivial, (hp.d_st.sub_left (VG.Proof.Poly1305.X86_64.blk_dR h.c_le)).symm,
      hp.stk_st.sub_left (fun x hx => hstk x (VG.Proof.Poly1305.X86_64.ret8_stk _ x hx)),
      hp.stk_st.sub_left (fun x hx => hstk x (VG.Proof.Poly1305.X86_64.callee_stk _ v.stack_le x hx)),
      (hp.stk_d.sub_left (fun x hx => hstk x (VG.Proof.Poly1305.X86_64.callee_stk _ v.stack_le x hx))).sub_right (VG.Proof.Poly1305.X86_64.blk_dR h.c_le), ?_⟩
    · have e := BitVec.toNat_add (VG.Proof.Poly1305.X86_64.dp s₀) (BitVec.ofNat 64 c)
      have e' : (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c).toNat ≤ (VG.Proof.Poly1305.X86_64.dp s₀).toNat + c := by
        rw [e, toNat_ofNat_lt (by omega_using [hdl, h.c_le])]; exact Nat.mod_le _ _
      have := hp.nowrap
      omega_using [e', this, hle]
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Poly1305.X86_64.dR s₀, by rw [h.rd, hp.rd]; exact List.mem_cons_self, c, rfl, hle⟩
    · exact ⟨sR (st s₀), by rw [h.wr, hp.wr]; exact List.mem_append_right _ List.mem_cons_self, 0,
        by simp, (Nat.zero_add _).le⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨sR (st s₀), by rw [h.wr]; exact hp.st_in, 0, by simp, (Nat.zero_add _).le⟩

/-- The call of an implementation of `vg_poly1305_blocks`, when there are
whole blocks: it keeps the callee-saved registers and the bits of MXCSR that
`abiPreserved` keeps. -/
theorem call_ok (hge : 16 ≤ VG.Proof.Poly1305.X86_64.dl s₀ - c) :
    WP isa (.call v.name v.code) s fun s' => VG.Proof.Poly1305.X86_64.After s₀ c s' ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hpre, hc, hw⟩ := VG.Proof.Poly1305.X86_64.call_pre v hp h
  have hle := VG.Proof.Poly1305.X86_64.blk_le h.c_le
  have hsp : s.gpr .rsp = s₀.gpr .rsp := h.rsp
  have hd := v.depth_le
  refine WP.call_mx (k := blocksStack v.stack) v.ok v.nosp (by omega_using [hd]) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩ hmx'
  have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := hcs
  have hf' : Frame [sR (st s₀), VG.Proof.Poly1305.X86_64.stkR s₀] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun x hx => ?_⟩
      rw [hsp] at hx
      exact below_sub (a := 8 * (v.code.depth + 1)) (b := 24) (by omega_using [hd]) (by decide) x hx
  -- The data absorbed, as on entry.
  have hblk : bytesAt s.callEntry.mem (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c) (16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16)) =
      bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c) (16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16)) := by
    have hdl := VG.Proof.Poly1305.X86_64.dl_lt s₀
    rw [Poly1305.bytesAt_frame (VG.Proof.Poly1305.X86_64.callEntry_frame s) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hsp]
        exact ((hp.stk_d.sub_left (VG.Proof.Poly1305.X86_64.ret8_stk _)).sub_right (VG.Proof.Poly1305.X86_64.blk_dR h.c_le)).symm)
      (by omega_using [hdl, hle])]
    refine Poly1305.bytesAt_frame h.frame (fun r hr => ?_) (by omega_using [hdl, hle])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.d_st.sub_left (VG.Proof.Poly1305.X86_64.blk_dR h.c_le)
    · exact hp.d_sc.sub_left (VG.Proof.Poly1305.X86_64.blk_dR h.c_le)
  simp only [blocksStack, Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx, VG.Proof.Poly1305.X86_64.blk_toNat, hm₂, hblk] at hpost
  obtain ⟨X, Y, hX, hY, hXY, hYd, hbuf, hrep⟩ := h.st
  have hY0 : Y = [] := hYd.resolve_right (by omega_using [hge])
  subst hY0
  refine ⟨{ rbx := by rw [cs _ (by simp [calleeSaved]), h.rbx]
            rbp := by rw [cs _ (by simp [calleeSaved]), h.rbp]
            r12 := by rw [cs _ (by simp [calleeSaved]), h.r12]
            r15 := by rw [cs _ (by simp [calleeSaved]), h.r15]
            rsp := by rw [cs _ (by simp [calleeSaved]), hsp]
            rd := hrd.trans h.rd
            wr := hwr.trans h.wr
            frame := (h.frame.mono (by simp)).trans (hf'.mono (by simp))
            saved := h.saved.frame hf' (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · exact hp.st_sc.symm
              · exact hp.stk_sc.symm)
            c_le := h.c_le
            st := ⟨X ++ bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c) (16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16)), [], ?_, by decide,
              ?_, .inl rfl, rfl, fun key W hr => ?_⟩ }, cs, hmx'⟩
  · simp only [List.length_append, Poly1305.length_bytesAt]; omega_using [hX]
  · rw [List.append_nil, VG.Proof.Poly1305.X86_64.Dt, Poly1305.bytesAt_add, ← List.append_assoc]
    rw [List.append_nil] at hXY
    rw [hXY]
  · have := hpost key (W ++ X) (VG.Proof.Poly1305.X86_64.repr_frame (VG.Proof.Poly1305.X86_64.callEntry_frame s) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [hsp]
      exact (hp.stk_st.sub_left (VG.Proof.Poly1305.X86_64.ret8_stk _)).symm.sub_left (VG.Proof.Poly1305.X86_64.rpR_sub _)) (hrep key W hr))
    rw [List.append_assoc] at this
    exact this

end

/-! ## After the call -/

theorem wp_andi {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_add {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- Before copying the rest: `d` bytes of data consumed, fewer than 16 left. -/
structure Res (s₀ : State) (d : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 d
  rcx : s.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀ - d)
  d_le : d ≤ VG.Proof.Poly1305.X86_64.dl s₀
  lt : VG.Proof.Poly1305.X86_64.dl s₀ - d < 16
  r15 : s.gpr .r15 = VG.Proof.Poly1305.X86_64.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀, VG.Proof.Poly1305.X86_64.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.Poly1305.X86_64.SavedAt (VG.Proof.Poly1305.X86_64.scr s₀) s₀ s.mem
  st : VG.Proof.Poly1305.X86_64.StOk s₀ d s.mem

theorem resume_ok {s₀ : State} {c : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.After s₀ c s) :
    WP isa (.block resume) s (VG.Proof.Poly1305.X86_64.Res s₀ (c + 16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16))) := by
  have hdl := VG.Proof.Poly1305.X86_64.dl_lt s₀
  have hc := h.c_le
  unfold resume
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => VG.Proof.Poly1305.X86_64.wp_andi fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_sub fun s₅ u₅ => VG.Proof.Poly1305.X86_64.wp_add fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdi → r ≠ .rcx → r ≠ .rsi → s₆.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₆.other r h3, u₅.other r h3, u₄.other r h3, u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have mem₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rcx₆ : s₆.gpr .rcx = BitVec.ofNat 64 ((VG.Proof.Poly1305.X86_64.dl s₀ - c) % 16) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
      u₁.other _ (by decide), h.r12, and15, toNat_ofNat_lt (by omega_using [hdl])]
  have hm : (VG.Proof.Poly1305.X86_64.dl s₀ - c) % 16 ≤ VG.Proof.Poly1305.X86_64.dl s₀ - c := Nat.mod_le _ _
  have e : VG.Proof.Poly1305.X86_64.dl s₀ - c - (VG.Proof.Poly1305.X86_64.dl s₀ - c) % 16 = 16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16) := by
    have := Nat.div_add_mod (VG.Proof.Poly1305.X86_64.dl s₀ - c) 16; omega_using [this]
  have hle : c + 16 * ((VG.Proof.Poly1305.X86_64.dl s₀ - c) / 16) ≤ VG.Proof.Poly1305.X86_64.dl s₀ := VG.Proof.Poly1305.X86_64.blk_le hc
  exact {
    rdi := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; exact h.rbx
    rsi := by
      have r12₃ : s₃.gpr .r12 = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.dl s₀ - c) := by
        rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r12]
      have rcx₄ : s₄.gpr .rcx = BitVec.ofNat 64 ((VG.Proof.Poly1305.X86_64.dl s₀ - c) % 16) := by
        rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), h.r12, and15,
          toNat_ofNat_lt (by omega_using [hdl])]
      have rbp₅ : s₅.gpr .rbp = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 c := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h.rbp]
      rw [u₆.gpr, u₅.gpr, u₄.gpr, r12₃, rcx₄, rbp₅, sub_ofNat hm, e, BitVec.add_comm, BitVec.add_assoc,
        ← BitVec.ofNat_add]
    rcx := by
      rw [rcx₆]; congr 1
      have := Nat.div_add_mod (VG.Proof.Poly1305.X86_64.dl s₀ - c) 16; omega_using [this, hc]
    d_le := hle
    lt := by have := Nat.div_add_mod (VG.Proof.Poly1305.X86_64.dl s₀ - c) 16; have := Nat.mod_lt (VG.Proof.Poly1305.X86_64.dl s₀ - c) (show 16 > 0 by decide)
             omega_using [this, hc]
    r15 := by rw [g _ (by decide) (by decide) (by decide)]; exact h.r15
    rsp := by rw [g _ (by decide) (by decide) (by decide)]; exact h.rsp
    rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact h.rd
    wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr
    frame := by rw [mem₆]; exact h.frame
    saved := by rw [mem₆]; exact h.saved
    st := by rw [mem₆]; exact h.st }

/-- When all the data is consumed. -/
structure Fin (s₀ : State) (s : State) : Prop where
  r15 : s.gpr .r15 = VG.Proof.Poly1305.X86_64.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (st s₀), VG.Proof.Poly1305.X86_64.scR s₀, VG.Proof.Poly1305.X86_64.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.Poly1305.X86_64.SavedAt (VG.Proof.Poly1305.X86_64.scr s₀) s₀ s.mem
  st : VG.Proof.Poly1305.X86_64.StOk s₀ (VG.Proof.Poly1305.X86_64.dl s₀) s.mem

theorem Res.srcOk {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {d : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.Res s₀ d s) :
    SrcOk s s₀.mem (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 d) (VG.Proof.Poly1305.X86_64.dl s₀ - d) := by
  intro i hi
  have hdl := VG.Proof.Poly1305.X86_64.dl_lt s₀
  have hd := h.d_le
  have e : VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 d + BitVec.ofNat 64 i = VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 (d + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e]
  have hc : (VG.Proof.Poly1305.X86_64.dR s₀).Contains (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 (d + i)) 1 := VG.Proof.Poly1305.X86_64.dR_contains s₀ (by omega_using [hi, hd])
  refine ⟨⟨VG.Proof.Poly1305.X86_64.dR s₀, by rw [h.rd, hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _), hc⟩,
    fun hb => ?_, ?_⟩
  · rw [h.rdi] at hb
    exact hp.d_st _ hc (VG.Proof.Poly1305.X86_64.bfR_sub_sR _ _ hb)
  · refine h.frame.bytes (R := VG.Proof.Poly1305.X86_64.dR s₀) (fun r hr => ?_) (show VG.Proof.Poly1305.X86_64.dl s₀ ≤ 2 ^ 64 by omega_using [hdl])
      (show d + i < VG.Proof.Poly1305.X86_64.dl s₀ by omega_using [hi, hd])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.d_st
    · exact hp.d_sc
    · exact hp.stk_d.symm

theorem Res.flags {s₀ : State} {d : Nat} {s s' : State} (h : VG.Proof.Poly1305.X86_64.Res s₀ d s) (hf : VG.Proof.Poly1305.X86_64.FlagsOnly s s') :
    VG.Proof.Poly1305.X86_64.Res s₀ d s' :=
  { rdi := by rw [hf.1]; exact h.rdi, rsi := by rw [hf.1]; exact h.rsi, rcx := by rw [hf.1]; exact h.rcx
    d_le := h.d_le, lt := h.lt, r15 := by rw [hf.1]; exact h.r15, rsp := by rw [hf.1]; exact h.rsp
    rd := by rw [hf.2.2.1]; exact h.rd, wr := by rw [hf.2.2.2]; exact h.wr
    frame := by rw [hf.2.1]; exact h.frame, saved := by rw [hf.2.1]; exact h.saved
    st := by rw [hf.2.1]; exact h.st }

theorem rest_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {d : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.Res s₀ d s) :
    WP isa rest s (VG.Proof.Poly1305.X86_64.Fin s₀) := by
  have hdl := VG.Proof.Poly1305.X86_64.dl_lt s₀
  have hd := h.d_le
  refine WP.seq (wp_test fun s₁ g₁ m₁ rd₁ wr₁ z₁ => WP.block_nil ?_)
  have h₁ := h.flags ⟨g₁, m₁, rd₁, wr₁⟩
  refine WP.ite (s.gpr .rcx &&& s.gpr .rcx == 0) (by simp only [eval, z₁]) (fun hb => ?_) (fun hb => ?_)
  · rw [BitVec.and_self, h.rcx, ofNat_beq_zero (by omega_using [hdl])] at hb
    simp only [decide_eq_true_eq] at hb
    have e : d = VG.Proof.Poly1305.X86_64.dl s₀ := by omega_using [hb, hd]
    subst e
    exact WP.block_nil ⟨h₁.r15, h₁.rsp, h₁.rd, h₁.wr, h₁.frame, h₁.saved, h₁.st⟩
  · rw [BitVec.and_self, h.rcx, ofNat_beq_zero (by omega_using [hdl])] at hb
    simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (wp_mov32i fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_)
    have hg : ∀ r, r ≠ .rax → r ≠ .r12 → s₃.gpr r = s₁.gpr r := fun r h1 h2 => by
      rw [u₃.other r h1, u₂.other r h2]
    have hm₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
    have hrd₃ : s₃.rd = s₁.rd := by rw [u₃.rd, u₂.rd]
    have hwr₃ : s₃.wr = s₁.wr := by rw [u₃.wr, u₂.wr]
    have h₃ : VG.Proof.Poly1305.X86_64.Res s₀ d s₃ :=
      { rdi := by rw [hg _ (by decide) (by decide)]; exact h₁.rdi
        rsi := by rw [hg _ (by decide) (by decide)]; exact h₁.rsi
        rcx := by rw [hg _ (by decide) (by decide)]; exact h₁.rcx
        d_le := hd, lt := h.lt
        r15 := by rw [hg _ (by decide) (by decide)]; exact h₁.r15
        rsp := by rw [hg _ (by decide) (by decide)]; exact h₁.rsp
        rd := by rw [hrd₃]; exact h₁.rd, wr := by rw [hwr₃]; exact h₁.wr
        frame := by rw [hm₃]; exact h₁.frame, saved := by rw [hm₃]; exact h₁.saved
        st := by rw [hm₃]; exact h₁.st }
    have hw : sR (s₃.gpr .rdi) ∈ s₃.wr := by rw [h₃.wr, h₃.rdi]; exact hp.st_in
    refine WP.mono (copy_ok (j0 := 0) (n := VG.Proof.Poly1305.X86_64.dl s₀ - d) (by omega_using [h.lt]) (by omega_using [hb]) hw
      (h₃.srcOk hp) h₃.rsi (by rw [u₃.other _ (by decide), u₂.gpr]; rfl)
      (by rw [u₃.gpr, u₂.other _ (by decide), h₁.rcx])) fun s' hcp => ?_
    have hk : ∀ r, r ≠ .rsi → r ≠ .r12 → r ≠ .rax → r ≠ .r13 → s'.gpr r = s₃.gpr r := hcp.keep
    have hf : Frame [bfR (st s₀)] s₃.mem s'.mem := by rw [← h₃.rdi]; exact hcp.frame (by omega_using [h.lt])
    obtain ⟨X, Y, hX, hY, hXY, hYd, _, hrep⟩ := h₃.st
    have hY0 : Y = [] := hYd.resolve_right (by omega_using [hb])
    subst hY0
    have hlen : (bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 d) (VG.Proof.Poly1305.X86_64.dl s₀ - d)).length = VG.Proof.Poly1305.X86_64.dl s₀ - d :=
      Poly1305.length_bytesAt _ _ _
    refine { r15 := by rw [hk _ (by decide) (by decide) (by decide) (by decide)]; exact h₃.r15
             rsp := by rw [hk _ (by decide) (by decide) (by decide) (by decide)]; exact h₃.rsp
             rd := hcp.rd.trans h₃.rd
             wr := hcp.wr.trans h₃.wr
             frame := h₃.frame.trans (hf.sub fun r hr => by
               simp only [List.mem_singleton] at hr; subst hr
               exact ⟨_, List.mem_cons_self, VG.Proof.Poly1305.X86_64.bfR_sub_sR _⟩)
             saved := h₃.saved.frame hf (fun r hr => by
               simp only [List.mem_singleton] at hr; subst hr
               exact hp.st_sc.symm.sub_right (VG.Proof.Poly1305.X86_64.bfR_sub_sR _))
             st := ⟨X, bytesAt s₀.mem (VG.Proof.Poly1305.X86_64.dp s₀ + BitVec.ofNat 64 d) (VG.Proof.Poly1305.X86_64.dl s₀ - d), hX,
               by omega_using [hlen, h.lt], ?_, .inr rfl, ?_, fun key W hr => ?_⟩ }
    · rw [List.append_nil] at hXY
      rw [VG.Proof.Poly1305.X86_64.Dt, show VG.Proof.Poly1305.X86_64.dl s₀ = d + (VG.Proof.Poly1305.X86_64.dl s₀ - d) by omega_using [hd], Poly1305.bytesAt_add, ← List.append_assoc,
        ← VG.Proof.Poly1305.X86_64.Dt, hXY, show d + (VG.Proof.Poly1305.X86_64.dl s₀ - d) - d = VG.Proof.Poly1305.X86_64.dl s₀ - d by omega_using [hd]]
    · have hb' := hcp.buf (by omega_using [h.lt])
      rw [h₃.rdi, Nat.zero_add] at hb'
      rw [hlen, hb']
      rfl
    · refine VG.Proof.Poly1305.X86_64.repr_frame hf (fun r hr' => ?_) (hrep key W hr)
      simp only [List.mem_singleton] at hr'; subst hr'
      exact VG.Proof.Poly1305.X86_64.rpR_bfR _

/-! ## Restoring the registers -/

theorem ret_stkR (s₀ : State) : (retR s₀).Disjoint (VG.Proof.Poly1305.X86_64.stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 24) (d := 24) (n := 8) (k := 24)
    (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem fin_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {s : State} (h : VG.Proof.Poly1305.X86_64.Fin s₀ s) :
    WP isa (.block restoreS) s fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.updateX86_64.post s₀ s' := by
  refine WP.mono (Spill.restore_ok .r15 savedS s₀.gpr s (by decide) (fun q hq => ⟨VG.Proof.Poly1305.X86_64.scR s₀,
    by rw [h.rd, h.wr, hp.wr]; simp, by
      rw [h.r15]; exact Offset.contains_base _ (by have := VG.Proof.Poly1305.X86_64.savedS_bound q hq; omega)
        (by have := VG.Proof.Poly1305.X86_64.savedS_bound q hq; omega)⟩)
    (by rw [h.r15]; exact h.saved)) fun s' ⟨g₁, g₂, m', _⟩ => ?_
  refine ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h.rsp, ?_⟩, fun key msg hbuf hcnt => ?_⟩
  · rw [m']
    refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_st
    · exact hp.ret_sc
    · exact VG.Proof.Poly1305.X86_64.ret_stkR s₀
  · obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
    have hk : VG.Proof.Poly1305.X86_64.kb s₀ = (W ++ B).length % 16 := hcnt
    have hBf : VG.Proof.Poly1305.X86_64.Bf s₀ = B := by rw [VG.Proof.Poly1305.X86_64.Bf, hk, off_56, hBb]
    obtain ⟨X, Y, hX, hY, hXY, _, hbufY, hrepX⟩ := h.st
    have hr := hrepX key W hrep
    change Buffered s'.mem (st s₀) key (W ++ B ++ VG.Proof.Poly1305.X86_64.Dt s₀ (VG.Proof.Poly1305.X86_64.dl s₀))
    rw [List.append_assoc, ← hBf, hXY, ← List.append_assoc, m']
    exact Buffered.of hr hY (by rw [← off_56]; exact hbufY)

theorem updatePost_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) {c : Nat} {s : State} (h : VG.Proof.Poly1305.X86_64.After s₀ c s) :
    WP isa updatePost s fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.updateX86_64.post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.resume_ok h) fun _ h₁ => WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.rest_ok hp h₁) fun _ h₂ => VG.Proof.Poly1305.X86_64.fin_ok hp h₂))

/-! ## The whole function -/

theorem update_correct (v : BlocksImpl) {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.UPre s₀) :
    WP isa (update v.name v.code) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.updateX86_64.post s₀ s' := by
  refine WP.seq (WP.mono_mx (by lit_decide) (VG.Proof.Poly1305.X86_64.updatePre_ok hp) fun s₁ ⟨c, h₁⟩ mx₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s : State => VG.Proof.Poly1305.X86_64.After s₀ c s ∧ s.mxcsr.extractLsb' 6 10 = s₀.mxcsr.extractLsb' 6 10)
    ?_ fun s₂ ⟨h₂, mx₂⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.Poly1305.X86_64.dl s₀ - c < 16)) (by simp only [eval, h₁.cf]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨h₁.after hb, by rw [mx₁]⟩
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      exact WP.mono (VG.Proof.Poly1305.X86_64.call_ok v hp h₁ hb) fun s' ⟨ha, _, mx'⟩ => ⟨ha, by rw [mx', mx₁]⟩
  · exact WP.mono_mx (by lit_decide) (VG.Proof.Poly1305.X86_64.updatePost_ok hp h₂) fun s₃ ⟨hg, hpost⟩ mx₃ =>
      ⟨⟨hg.1, hg.2, by rw [mx₃]; exact mx₂⟩, hpost⟩

theorem update_ok (v : BlocksImpl) (s : State) (hs : Proof.Poly1305.updateX86_64.pre s) :
    ∃ t s', Exec isa (update v.name v.code) s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.updateX86_64.post s s' :=
  VG.Proof.Poly1305.X86_64.update_correct v (UPre.of s hs)

end VG.Proof.Poly1305.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.UpdateVerified`. -/
section

/-!
# Poly1305 on x86-64: `update`, constant time and `Verified`

`update` calls an implementation of `vg_poly1305_blocks` that the proof does
not know, so the taint analysis cannot follow it into it. The code before the
call (`updatePre`) and the code after it (`updatePost`) are checked by the
taint analysis; the call is constant time by the implementation's own proof
(`RelCT.callEx`), since its arguments agree in two runs (the analysis of
`updatePre` says so) and correctness says it may access the regions it is
given; and after it, the registers the code after it needs are public again,
since the callee keeps them (`calleeSaved`).
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64

/-! ## Constant time -/

/-- The public registers and what is known about memory on entry: the
lengths of the state and `scratch`, and the registers holding their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [128, 128],
    bases := [(.rdi, 0, 0), (.r8, 1, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.updateX86_64.pre s₁)
    (h₂ : Proof.Poly1305.updateX86_64.pre s₂) (hpub : Proof.Poly1305.updateX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree VG.Proof.Poly1305.X86_64.τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, Proof.Poly1305.updateX86_64.pre s → X86_64.Taint.Wf VG.Proof.Poly1305.X86_64.τ₀ s := by
    intro s hs
    obtain ⟨-, hw, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Poly1305.X86_64.τ₀], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [VG.Proof.Poly1305.X86_64.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.Poly1305.X86_64.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [VG.Proof.Poly1305.X86_64.τ₀] at h
  · intro sl h; simp [VG.Proof.Poly1305.X86_64.τ₀] at h

/-- What the code before the call leaves public: the arguments of the call,
what is kept across it, and the flags. -/
abbrev preRegs : List Reg := [.rdi, .rsi, .rdx, .rbx, .rbp, .r12, .r15, .rsp]

/-- What the code after the call needs public: what the call keeps. -/
abbrev postRegs : List Reg := [.rbx, .rbp, .r12, .r15, .rsp]

theorem updatePre_taint : ∃ h, ((taint.check VG.Proof.Poly1305.X86_64.τ₀ updatePre h).map fun τ' =>
    (RegSet.ofList VG.Proof.Poly1305.X86_64.preRegs).subset τ'.regs && τ'.flags) = some true :=
  ⟨_, by taint_decide⟩

theorem updatePost_taint : ∃ h, (taint.check (Taint.ofRegs VG.Proof.Poly1305.X86_64.postRegs) updatePost h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem none_taint : ∃ h, ((taint.check (Taint.ofRegs VG.Proof.Poly1305.X86_64.postRegs) (.block []) h).map fun τ' =>
    (RegSet.ofList VG.Proof.Poly1305.X86_64.postRegs).subset τ'.regs) = some true :=
  ⟨_, by taint_decide⟩

/-- Code the taint analysis proves constant time, which leaves the registers
`rs` and the flags public. -/
theorem RelCT.taintFlags {τ : X86_64.Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → X86_64.Taint.Agree τ s₁ s₂) (rs : List Reg) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ'.regs && τ'.flags) = some true) :
    RelCT isa P c fun s₁ s₂ => (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ s₁.cf = s₂.cf := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  simp only [Bool.and_eq_true] at hs
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, fun r hr => ha.rf.1 r (RegSet.mem_of_subset hs.1 (RegSet.mem_ofList.mpr hr)), (ha.rf.2 hs.2).1⟩

section
variable (v : BlocksImpl) {s₀ s₀' : State} (h₀ : Proof.Poly1305.updateX86_64.pre s₀)
  (h₀' : Proof.Poly1305.updateX86_64.pre s₀') (hq : Proof.Poly1305.updateX86_64.pub s₀ s₀')
include h₀ h₀' hq

/-- Before the call, in two runs. -/
def Mid (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ((∀ r ∈ VG.Proof.Poly1305.X86_64.preRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.cf = s₂.cf) ∧ (∃ c, VG.Proof.Poly1305.X86_64.Ready s₀ c s₁) ∧ (∃ c, VG.Proof.Poly1305.X86_64.Ready s₀' c s₂)

omit hq in
/-- The call, or none. -/
theorem mid_rel : RelCT isa (VG.Proof.Poly1305.X86_64.Mid s₀ s₀') (.ite .b (.block []) (.call v.name v.code))
    fun s₁ s₂ => ∀ r ∈ VG.Proof.Poly1305.X86_64.postRegs, s₁.gpr r = s₂.gpr r := by
  have hp := UPre.of _ h₀
  have hp' := UPre.of _ h₀'
  have sub : ∀ r ∈ VG.Proof.Poly1305.X86_64.postRegs, r ∈ VG.Proof.Poly1305.X86_64.preRegs := by decide
  refine RelCT.ite (fun s₁ s₂ h => by simp only [eval, h.1.2]) ?_ ?_
  · obtain ⟨_, hn⟩ := VG.Proof.Poly1305.X86_64.none_taint
    exact RelCT.taintRegs (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => h.1.1.1 r (sub r hr)) VG.Proof.Poly1305.X86_64.postRegs hn
  · have ct := RelCT.callEx (n := v.name) (k := blocksStack v.stack)
      (P := fun s₁ s₂ => VG.Proof.Poly1305.X86_64.Mid s₀ s₀' s₁ s₂ ∧ eval .b s₁ = some false) v.ok v.ct
      fun s₁ s₂ ⟨⟨⟨hr, _⟩, ⟨c₁, r₁⟩, ⟨c₂, r₂⟩⟩, _⟩ => by
        obtain ⟨p₁, cv₁, w₁⟩ := VG.Proof.Poly1305.X86_64.call_pre v hp r₁
        obtain ⟨p₂, cv₂, w₂⟩ := VG.Proof.Poly1305.X86_64.call_pre v hp' r₂
        refine ⟨_, _, _, _, p₁, p₂, ?_, cv₁, w₁, cv₂, w₂, hr .rsp (by simp)⟩
        simp only [blocksStack, Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.callEntry_rsp,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp)]
        exact ⟨⟨hr .rdi (by simp), hr .rsi (by simp), hr .rdx (by simp)⟩, by rw [hr .rsp (by simp)]⟩
    have keep : ∀ {σ₀ s : State}, VG.Proof.Poly1305.X86_64.UPre σ₀ → (∃ c, VG.Proof.Poly1305.X86_64.Ready σ₀ c s) → eval .b s = some false →
        WP isa (.call v.name v.code) s fun s' => ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := by
      intro σ₀ s hp ⟨c, h⟩ he
      rw [eval, h.cf] at he
      simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at he
      exact WP.mono (VG.Proof.Poly1305.X86_64.call_ok v hp h he) fun _ h' => h'.2.1
    refine (ct.wpDep (F := fun (σ s' : State) => ∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r) fun s₁ s₂ h =>
      ⟨keep hp h.1.2.1 h.2, keep hp' h.1.2.2 (by simp only [eval] at h ⊢; rw [← h.1.1.2]; exact h.2)⟩).mono
      (fun _ _ h => h) ?_
    rintro s₁' s₂' ⟨_, σ₁, σ₂, ⟨⟨⟨hr, _⟩, _⟩, _⟩, k₁, k₂⟩ r hr'
    have hc : r ∈ calleeSaved := by
      simp only [VG.Proof.Poly1305.X86_64.postRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]
    rw [k₁ r hc, k₂ r hc, hr r (sub r hr')]

theorem update_rel :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (update v.name v.code) fun _ _ => True := by
  have hp := UPre.of _ h₀
  have hp' := UPre.of _ h₀'
  obtain ⟨_, hpre⟩ := VG.Proof.Poly1305.X86_64.updatePre_taint
  obtain ⟨_, hpost⟩ := VG.Proof.Poly1305.X86_64.updatePost_taint
  have pre := ((RelCT.taintFlags (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
    (fun _ _ h => h.1 ▸ h.2 ▸ VG.Proof.Poly1305.X86_64.agree₀ h₀ h₀' hq) VG.Proof.Poly1305.X86_64.preRegs hpre).wp
    (F₁ := fun s => ∃ c, VG.Proof.Poly1305.X86_64.Ready s₀ c s) (F₂ := fun s => ∃ c, VG.Proof.Poly1305.X86_64.Ready s₀' c s) fun _ _ h =>
      ⟨by rw [h.1]; exact VG.Proof.Poly1305.X86_64.updatePre_ok hp, by rw [h.2]; exact VG.Proof.Poly1305.X86_64.updatePre_ok hp'⟩)
  have post := RelCT.taint (A := taint) (P := fun s₁ s₂ => ∀ r ∈ VG.Proof.Poly1305.X86_64.postRegs, s₁.gpr r = s₂.gpr r)
    (Taint.ofRegs VG.Proof.Poly1305.X86_64.postRegs) (fun _ _ h => Taint.agree_ofRegs h) hpost
  exact pre.seq ((VG.Proof.Poly1305.X86_64.mid_rel v h₀ h₀').seq post)

end

theorem update_ct (v : BlocksImpl) :
    ConstantTime isa Proof.Poly1305.updateX86_64.pre Proof.Poly1305.updateX86_64.pub (update v.name v.code) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (VG.Proof.Poly1305.X86_64.update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- A state satisfying the precondition (with no data). -/
def updateSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rsp => 0x4000 | .r8 => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x5000, 128⟩]

theorem update_verified (v : BlocksImpl) :
    Verified X86_64.target (update v.name v.code) (Proof.Poly1305.updateScratchContract X86_64.abi 24) :=
  Verified.of_correct (VG.Proof.Poly1305.X86_64.update_ok v) (VG.Proof.Poly1305.X86_64.update_ct v)
    { pre := by
        sig_implies_pre [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig, Spec.Poly1305.updatePost,
          Proof.Poly1305.updateX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig, Spec.Poly1305.updatePost, X86_64.abi, X86_64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig, Spec.Poly1305.updatePost,
          Proof.Poly1305.updateX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig, Spec.Poly1305.updatePost, X86_64.abi,
          X86_64.argRegs, Proof.Poly1305.X86_64.updateSat]
          [Proof.Poly1305.X86_64.updateSat] using Proof.Poly1305.X86_64.updateSat }

/-- `update` never writes the stack pointer. -/
theorem update_spSafe (v : BlocksImpl) :
    (update v.name v.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [update, Code.all, v.spSafe, Bool.and_true]
  lit_decide

end VG.Proof.Poly1305.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Frame`. -/
section

/-!
# Streaming Poly1305 on x86-64, with its working space on the stack

`update` and `finalize` run their code, proved with the working space as an
argument, in a frame of 136 bytes that allocates it (`Verified.stackScratch`):
the 128 bytes of working space, and 8 more to keep `rsp` aligned. `update`'s
call of `vg_poly1305_blocks` uses 24 bytes below it, as before.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

theorem fill_xdepth : Impl.Poly1305.X86_64.fill.x86_64Depth = 0 := by decide +kernel
theorem rest_xdepth : Impl.Poly1305.X86_64.rest.x86_64Depth = 0 := by decide +kernel

theorem update_xdepth (v : BlocksImpl) :
    (Impl.Poly1305.X86_64.update v.name v.code).x86_64Depth ≤ 24 := by
  have := v.xdepth
  have := v.stack_le
  simp only [Impl.Poly1305.X86_64.update, Impl.Poly1305.X86_64.updatePre,
    Impl.Poly1305.X86_64.updatePost, Code.x86_64Depth, VG.Proof.Poly1305.X86_64.fill_xdepth, VG.Proof.Poly1305.X86_64.rest_xdepth, Nat.max_le]
  omega

/-- A state satisfying `vg_poly1305_update`'s precondition, without the
working space. -/
def updateFrameSat : State := { VG.Proof.Poly1305.X86_64.updateSat with
                                               wr := [⟨0x1000, 128⟩] }

theorem updateFrameSat_pre : ∃ s, (Spec.Poly1305.updateContract X86_64.abi 160).pre s := by
  implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Spec.Poly1305.updatePost,
    X86_64.abi, X86_64.argRegs] [updateFrameSat, updateSat] using VG.Proof.Poly1305.X86_64.updateFrameSat

theorem update_framed (v : BlocksImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 136 .r8 (Impl.Poly1305.X86_64.update v.name v.code))
      (Spec.Poly1305.updateContract X86_64.abi 160) :=
  X86_64.Verified.stackScratch (sig := Spec.Poly1305.updateSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.updatePost X86_64.abi.ptrBits) (wa := false) (stack := 24)
    (bytes := 136) (VG.Proof.Poly1305.X86_64.update_verified v) (by decide) (by decide) (by decide) (VG.Proof.Poly1305.X86_64.update_spSafe v)
    (VG.Proof.Poly1305.X86_64.update_xdepth v) VG.Proof.Poly1305.X86_64.updateFrameSat_pre

/-- A state satisfying `vg_poly1305_finalize`'s precondition, without the
working space. -/
def finalizeFrameSat : State := { finalizeSat with wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩] }

theorem finalizeFrameSat_pre : ∃ s, (Spec.Poly1305.finalizeContract X86_64.abi 136).pre s := by
  implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
    Spec.Poly1305.finalizePost, X86_64.abi, X86_64.argRegs] [finalizeFrameSat, finalizeSat]
    using VG.Proof.Poly1305.X86_64.finalizeFrameSat

theorem finalize_framed :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize)
      (Spec.Poly1305.finalizeContract X86_64.abi 136) :=
  X86_64.Verified.stackScratch (sig := Spec.Poly1305.finalizeSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.finalizePost X86_64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 136) finalize_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) VG.Proof.Poly1305.X86_64.finalizeFrameSat_pre

end VG.Proof.Poly1305.X86_64

end
