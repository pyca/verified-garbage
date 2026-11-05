module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreTable
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State
public import VerifiedGarbage.Proof.Ffdh.X86.Dom
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Table
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# FFDH's key-generation context on i686: the width

The precomputation's front: the vetted groups' recognized width of the
domain (`recognize_ok`, `VettedValidation.scan` in a frame of its three
arguments), to the header word at 48.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Precompute
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Impl.Ffdh.X86 (tbOff ldOff tOff)

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A word of a frame of 16 bytes below `sp`, within the 96 bytes below it. -/
theorem alloc_contains {sp : BitVec 32} (low : 96 ≤ sp.toNat) {d : Nat} (hd : d + 4 ≤ 16) :
    (below sp 96).Contains ((sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 d).setWidth 64) 4 := by
  have hE := sp.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

/-- The frame of 16 bytes below `sp`, within the 96 bytes below it. -/
theorem alloc_sub {sp : BitVec 32} (low : 96 ≤ sp.toNat) :
    Region.Sub ⟨(sp - BitVec.ofNat 32 16).setWidth 64, 16⟩ (below sp 96) := by
  have e16 : (sp - BitVec.ofNat 32 16).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 16 :=
    VG.X86.Taint.sub_setWidth (by omega)
  have e96 : (sp - BitVec.ofNat 32 96).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 96 :=
    VG.X86.Taint.sub_setWidth (by omega)
  simp only [below]
  rw [e16, e96]
  exact Offset.sub_below _ (by decide) (by decide)

/-- The four bytes below `sp`, within the 96 below it. -/
theorem below4_sub {sp : BitVec 32} (low : 96 ≤ sp.toNat) : Region.Sub (below sp 4) (below sp 96) := by
  have e4 : (sp - BitVec.ofNat 32 4).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 4 :=
    VG.X86.Taint.sub_setWidth (by omega)
  have e96 : (sp - BitVec.ofNat 32 96).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 96 :=
    VG.X86.Taint.sub_setWidth (by omega)
  simp only [below]
  rw [e4, e96]
  exact Offset.sub_below _ (by decide) (by decide)

/-- A synthetic argument, read in a frame of `4 k` bytes below the stack pointer of `s`. -/
theorem arg_in (h : In Ex base bytes len args s) {t : State} {i k : Nat} (hi : i < 18)
    (sp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * k)) (rd : t.rd = s.rd) (wr : ∀ r ∈ s.wr, r ∈ t.wr)
    (F : Frame [below (s.gpr .esp) 96] s.mem t.mem) :
    readSrc t (.mem (argAt k i)) = some (args i) := by
  have R := h.arg hi
  have top := h.top
  have hE := (s.gpr .esp).isLt
  have low := h.room.low
  have ea : t.ea (argAt k i) = s.ea (argAt 0 i) := by
    simp only [State.ea, argAt, at_, sp]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have eaS : s.ea (argAt 0 i) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
    simp only [argAt, at_]
    rw [ea_mk, addr_eq (by omega_arith)]
    simp only [Nat.mul_zero, Nat.add_zero]
  change t.load32 (t.ea _) = _
  change s.load32 (s.ea _) = _ at R
  rw [ea]
  simp only [State.load32] at R ⊢
  split at R
  · rename_i hin
    have hin' : InRegions (t.rd ++ t.wr) (s.ea (argAt 0 i)) 4 := by
      obtain ⟨q, hq, hc⟩ := hin
      refine ⟨q, ?_, hc⟩
      rw [rd]
      rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (wr _ hq)
    simp only [hin', ↓reduceIte]
    rw [F.readW (r := ⟨s.ea (argAt 0 i), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [eaS]
      simp only [below]
      rw [VG.X86.Taint.sub_setWidth (by omega_arith)]
      exact Offset.disjoint_below _ (by omega_arith)) (by decide)]
    exact R
  · cases R

/-- Bytes of a frame of 16 bytes below `sp`. -/
theorem alloc_in {sp : BitVec 32} (low : 96 ≤ sp.toNat) {d n : Nat} (hd : d + n ≤ 16) :
    (⟨(sp - BitVec.ofNat 32 16).setWidth 64, 16⟩ : Region).Contains (addr (sp - BitVec.ofNat 32 16) d) n := by
  have hE := sp.isLt
  simp only [addr, Region.Contains, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

/-- Two words of a frame of 16 bytes. -/
theorem alloc_rw {m : Mem} {p : BitVec 32} {a b : Nat} {v : BitVec 32} (apart : b + 4 ≤ a ∨ a + 4 ≤ b)
    (fit : p.toNat + 16 ≤ 2 ^ 32) (ha : a + 4 ≤ 16) (hb : b + 4 ≤ 16) :
    (m.writeW (addr p a) v).readW (addr p b) 32 = m.readW (addr p b) 32 := by
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Mem.readW_writeW_sep (Offset.sep _ apart (by omega) (by omega)) (by decide)

/-- Synthetic argument `i` to the word at `d` of a frame of 16 bytes below the stack pointer of `s`. -/
theorem pass_ok (h : In Ex base bytes len args s) {t : State} {i d : Nat} (hi : i < 18) (hd : d + 4 ≤ 16)
    (sp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16) (rd : t.rd = s.rd)
    (wr : t.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ :: s.wr)
    (F : Frame [below (s.gpr .esp) 96] s.mem t.mem) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Keeps [.eax] t u → u.syms = t.syms →
      u.mem = t.mem.writeW (addr (s.gpr .esp - BitVec.ofNat 32 16) d) (args i) →
      Frame [below (s.gpr .esp) 96] s.mem u.mem → WP isa (.block is) u Q) :
    WP isa (.block (.mov .eax (.mem (argAt 4 i)) :: .store (at_ .esp d) .eax :: is)) t Q := by
  have low := h.room.low
  refine wp_movS (arg_in h hi (k := 4) sp rd (fun r hr => by rw [wr]; exact List.mem_cons_of_mem _ hr) F)
    fun u₁ U₁ _ => ?_
  have ea : u₁.ea (at_ .esp d) = addr (s.gpr .esp - BitVec.ofNat 32 16) d := by
    show addr (u₁.gpr .esp) d = _
    rw [U₁.other _ (by decide), sp]
  refine wp_storeS ea ⟨_, by rw [U₁.wr, wr]; exact List.mem_cons_self .., alloc_in low hd⟩ fun u₂ M₂ => k u₂ ?_ ?_ ?_ ?_
  · exact U₁.keeps.trans ((M₂.keeps []).mono (by decide))
  · rw [M₂.syms, U₁.syms]
  · rw [M₂.mem, U₁.mem, U₁.gpr]
  · rw [M₂.mem, U₁.mem]
    exact F.writeW (List.mem_singleton_self _) _ (by
      have := alloc_contains low hd
      simpa only [addr] using this)

/-- Writes of the 96 bytes below `sp`, within a stage's ranges. -/
theorem stk_frameR {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem} (F : Frame [below sp 96] m m') :
    Frame (frameR base sp ws) m m' :=
  F.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..

/-- A header word stored. -/
theorem hdr_store (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun u =>
      In Ex base bytes len args u ∧ Outside base d 4 s.mem u.mem ∧ w32 u.mem base d = (s.gpr r).toNat ∧
      Keeps [] s u ∧ u.syms = s.syms := by
  have bl := h.bytes_lt
  have nd := h.need
  have nb : numBase = 3336 := rfl
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  refine wp_storeS (h.scratch.ea (d := d) (by omega_arith)) (h.scratch.write (d := d) (n := 4) (by omega_arith))
    fun u M => WP.block_nil ?_
  have O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  refine ⟨h.keep (M.keeps []) (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_arith)), O, ?_, M.keeps [],
    M.syms⟩
  rw [M.mem, w32_write_self]

/-- The vetted groups' table at `T`, from its bytes. -/
theorem tableAt_of {t : State} {T : BitVec 32} (read : InRegions (t.rd ++ t.wr) (byteAddr T) 17744)
    (bs : Spec.Rsa.bytesAt t.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes) :
    VettedValidation.TableAt (byteAddr T + BitVec.ofNat 64 0) VG.Impl.Ffdh.VettedGroups.groups t := by
  simp only [BitVec.add_zero]
  have e : (VG.Impl.Ffdh.VettedGroups.groups.flatMap VG.Impl.Ffdh.VettedGroups.Group.bytes).length = 17744 :=
    VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  refine VettedValidation.tableOfBytes _ _ t (by rw [e]; exact read) (by rw [e]; exact bs) (by rw [e]) ?_
  intro g hg
  simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A recognized width fits a word. -/
theorem recognize_lt (k : Nat) (dom : List Byte) :
    VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom < 2 ^ 32 := by
  have aux : ∀ gs : List VG.Impl.Ffdh.VettedGroups.Group, (∀ g ∈ gs, g.bits < 2 ^ 32) →
      VG.Impl.Ffdh.VettedGroups.recognizeList gs k dom < 2 ^ 32 := by
    intro gs
    induction gs with
    | nil => intro _; simp only [VG.Impl.Ffdh.VettedGroups.recognizeList]; decide
    | cons g gs ih =>
      intro hb
      simp only [VG.Impl.Ffdh.VettedGroups.recognizeList]
      split
      · exact hb g List.mem_cons_self
      · exact ih fun g' hg' => hb g' (List.mem_cons_of_mem _ hg')
  refine aux _ fun g hg => ?_
  simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The vetted groups' recognized width of the domain, to the header word at 48. -/
theorem recognize_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96)) {T : BitVec 32}
    (hT : s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = T) (tfit : T.toNat + 17744 ≤ 2 ^ 32)
    (tread : InRegions (s.rd ++ s.wr) (byteAddr T) 17744)
    (tbytes : Spec.Rsa.bytesAt s.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes)
    (tws : Region.Disjoint ⟨byteAddr T, 17744⟩ ⟨base, bytes⟩)
    (t40 : Region.Disjoint ⟨byteAddr T, 17744⟩ (below (s.gpr .esp) 96)) :
    WP isa recognize s fun u => Step Ex base bytes len args s u ∧ Kept base len [] [tbOff, recOff] s.mem u.mem ∧
      w32 u.mem base recOff = VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups len
        (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen) := by
  have low := h.room.low
  have top := h.top
  have hE := (s.gpr .esp).isLt
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nw := h.scratch.nowrap
  have dl := G.dl
  have lw := G.lower
  have up := G.upper
  have dfit := G.fit
  unfold recognize
  -- `ebx := edi`.
  refine WP.seq (wp_movS rfl fun s₁ U₁ _ => WP.block_nil ?_)
  have e1 : s₁.gpr .ebx = s.gpr .edi := U₁.gpr
  -- The table's address.
  refine WP.seq (WP.mono (symFrame_ok _ s₁ (by rw [U₁.other _ (by decide)]; omega)) fun s₂ R => ?_)
  have sp₂ : s₂.gpr .esp = s.gpr .esp := (R.gpr _ (by decide)).trans (U₁.other _ (by decide))
  have K₂ : Keeps [.eax, .ebx, .ecx] s s₂ := by
    refine ⟨fun r hr => ?_, R.rd.trans U₁.rd, R.wr.trans U₁.wr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.2⟩),
      U₁.other _ hr.2.1]
  have ebx₂ : s₂.gpr .ebx = s.gpr .edi := (R.gpr _ (by decide)).trans e1
  have eax₂ : s₂.gpr .eax = T := by rw [R.addr, U₁.syms, hT]
  have F₂ : Frame (frameR base (s.gpr .esp) (fR len)) s.mem s₂.mem := by
    have F := R.frame
    rw [U₁.mem, U₁.other _ (by decide)] at F
    exact F.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_cons_self .., below4_sub low⟩
  have h₂ : In Ex base bytes len args s₂ := h.keepF K₂ (by decide) (by decide) F₂ (fR_fit h)
  -- The table's address to the header.
  have ea₂ : s₂.ea ⟨.ebx, 16⟩ = off base 16 := by
    rw [ea_mk, ebx₂]; exact h.scratch.ea (d := 16) (by omega)
  refine WP.seq (wp_storeS ea₂ (h₂.scratch.write (d := 16) (n := 4) (by omega)) fun s₃ M₃ => WP.block_nil ?_)
  have O₃ : Outside base 16 4 s₂.mem s₃.mem := by rw [M₃.mem]; exact writeW32_outside _ _ _ (by omega)
  have K₃ : Keeps [.eax, .ebx, .ecx] s s₃ := K₂.trans ((M₃.keeps []).mono (by decide))
  have sp₃ : s₃.gpr .esp = s.gpr .esp := by rw [M₃.gpr, sp₂]
  have F₃ : Frame (frameR base (s.gpr .esp) (fR len)) s.mem s₃.mem :=
    F₂.trans (fR_of_outside h O₃ (.inl (by omega)))
  have h₃ : In Ex base bytes len args s₃ := h.keepF K₃ (by decide) (by decide) F₃ (fR_fit h)
  have tw₃ : s₃.mem.readW (off base 16) 32 = T := by rw [M₃.mem, Mem.readW_writeW_self32, eax₂]
  have Fs₂ : Frame [below (s.gpr .esp) 96] s.mem s₂.mem := by
    have F := R.frame
    rw [U₁.mem, U₁.other _ (by decide)] at F
    exact F.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_singleton_self _, below4_sub low⟩
  have k₃ : Kept base len [] [tbOff, recOff] s.mem s₃.mem :=
    ((kept_ops h (stk_frameR Fs₂) h.room).mono).trans (kept_word h (d := 16) (by omega) (by decide) O₃).mono
  -- The scan, in a frame of its three arguments.
  have p16 : 16 ≤ (s₃.gpr .esp).toNat := by rw [sp₃]; omega
  have hlen : ∀ m : Mem, (Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen).length = dlen := fun m => by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have ea16 : addr (s.gpr .edi) 16 = off base 16 := h.scratch.ea (d := 16) (by omega)
  have elen : (VG.Impl.Ffdh.VettedGroups.groups.flatMap VG.Impl.Ffdh.VettedGroups.Group.bytes).length = 17744 :=
    VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  refine WP.seq (WP.mono (WP.frameAlloc (bytes := 16) (Q := fun t => t.gpr .esp = s.gpr .esp ∧ t.rd = s₃.rd ∧
      t.wr = s₃.wr ∧ Frame [below (s.gpr .esp) 96] s₃.mem t.mem ∧
      t.gpr .eax = BitVec.ofNat 32 (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups len
        (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen)) ∧
      Keeps [.eax, .ecx, .edx, .esi, .edi, .ebp] s₃ t) (by decide) (by decide) (by decide) p16
    (NoSp.of_all (by rfl)) ?_) fun s₄ H₄ => ?_)
  · unfold scanArgs
    have aesp : (allocFrame 16 s₃).gpr .esp = s₃.gpr .esp - BitVec.ofNat 32 16 := allocFrame_esp _ _
    refine WP.seq (pass_ok h₃ (i := 2) (d := 4) (by decide) (by decide) aesp (allocFrame_rd _ _) (allocFrame_wr _ _)
      (by rw [allocFrame_mem]; exact Frame.refl _ _) fun u₁ K₁ Y₁ M₁ F₁ => ?_)
    refine pass_ok h₃ (i := 12) (d := 8) (by decide) (by decide) (by rw [K₁.1 _ (by decide), aesp])
      (by rw [K₁.2.1, allocFrame_rd]) (by rw [K₁.2.2, allocFrame_wr]) F₁ fun u₂ K₂' Y₂ M₂ F₂' => ?_
    refine pass_ok h₃ (i := 1) (d := 12) (by decide) (by decide)
      (by rw [K₂'.1 _ (by decide), K₁.1 _ (by decide), aesp]) (by rw [K₂'.2.1, K₁.2.1, allocFrame_rd])
      (by rw [K₂'.2.2, K₁.2.2, allocFrame_wr]) F₂' fun w Kw Yw Mw Fw => WP.block_nil ?_
    rw [sp₃] at Fw
    generalize hP : s.gpr .esp - BitVec.ofNat 32 16 = P at *
    have Pn : P.toNat = (s.gpr .esp).toNat - 16 := by rw [← hP]; exact VG.X86.sub_toNat (by omega)
    have wesp : w.gpr .esp = P := by
      rw [Kw.1 _ (by decide), K₂'.1 _ (by decide), K₁.1 _ (by decide), aesp, sp₃, hP]
    have wrd : w.rd = s.rd := by rw [Kw.2.1, K₂'.2.1, K₁.2.1, allocFrame_rd, K₃.2.1]
    have wwr : w.wr = ⟨P.setWidth 64, 16⟩ :: s.wr := by
      rw [Kw.2.2, K₂'.2.2, K₁.2.2, allocFrame_wr, sp₃, hP, K₃.2.2]
    have wmem : w.mem = ((s₃.mem.writeW (addr P 4) (args 2)).writeW (addr P 8) (args 12)).writeW (addr P 12)
        (args 1) := by
      rw [Mw, M₂, M₁, allocFrame_mem, sp₃, hP]
    have Pfit : P.toNat + 16 ≤ 2 ^ 32 := by omega
    have a0 : argAddr w 0 = addr P 4 := by show (w.gpr .esp + _).setWidth 64 = _; rw [wesp]; rfl
    have a1 : argAddr w 1 = addr P 8 := by show (w.gpr .esp + _).setWidth 64 = _; rw [wesp]; rfl
    have a2 : argAddr w 2 = addr P 12 := by show (w.gpr .esp + _).setWidth 64 = _; rw [wesp]; rfl
    have Fsw : Frame (frameR base (s.gpr .esp) (fR len)) s.mem w.mem := F₃.trans (stk_frameR Fw)
    have inw : ∀ {q : Addr} {n : Nat}, InRegions (s.rd ++ s.wr) q n → InRegions (w.rd ++ w.wr) q n := by
      intro q n ⟨r, hr, hc⟩
      refine ⟨r, ?_, hc⟩
      rw [wrd, wwr]
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    have C : VettedValidation.Context (s.gpr .edi) (args 2) P T len (Spec.Rsa.bytesAt w.mem (byteAddr (args 2)) dlen)
        w := by
      refine ⟨by rw [Kw.1 _ (by decide), K₂'.1 _ (by decide), K₁.1 _ (by decide), allocFrame_gpr _ _ (by decide),
          (M₃.gpr ▸ rfl : s₃.gpr .ebx = s₂.gpr .ebx), ebx₂], wesp, ?_, ?_, ?_, ?_, ?_, ?_, inw ?_, ?_, ?_, tfit, ?_,
        ?_, lw, up⟩
      · show w.mem.readW (argAddr w 0) 32 = _
        rw [a0, wmem, alloc_rw (.inl (by decide)) Pfit (by decide) (by decide),
          alloc_rw (.inl (by decide)) Pfit (by decide) (by decide), Mem.readW_writeW_self32]
      · show w.mem.readW (argAddr w 1) 32 = _
        rw [a1, wmem, alloc_rw (.inl (by decide)) Pfit (by decide) (by decide), Mem.readW_writeW_self32, hlen, G.e12]
      · show w.mem.readW (argAddr w 2) 32 = _
        rw [a2, wmem, Mem.readW_writeW_self32, h.outLen]
      · rw [a0]
        exact ⟨_, List.mem_append_right _ (by rw [wwr]; exact List.mem_cons_self ..), alloc_in (sp := s.gpr .esp)
          low (d := 4) (n := 12) (by decide) |> fun c => by rw [hP] at c; exact c⟩
      · rw [ea16]
        exact ⟨_, List.mem_append_right _ (by rw [wwr]; exact List.mem_cons_of_mem _ (by rw [← K₃.2.2]; exact h₃.ws.wr)),
          Offset.contains_base _ (by omega) (by omega)⟩
      · rw [ea16, Fw.readW (r := ⟨off base 16, 4⟩) (Region.contains_self _ _) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact h.room.apart.symm.sub_left (Offset.sub_base _ (by omega))) (by decide)]
        exact tw₃
      · rw [hlen]; exact G.rd
      · rw [hlen]
      · rw [hlen]; exact dfit
      · omega
      · rw [hlen]; exact dl
    have TA := tableAt_of (t := w) (inw tread) (by rw [KeyScan.bytes_keep h tws (by decide) t40 Fsw]; exact tbytes)
    refine WP.mono (VettedValidation.scan_ok _ 0 w C TA (by rw [elen])) fun t ⟨E, Mt, Kt⟩ => ?_
    have tesp : t.gpr .esp = P := (Kt.1 _ (by decide)).trans wesp
    have dw : Spec.Rsa.bytesAt w.mem (byteAddr (args 2)) dlen = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen :=
      KeyScan.bytes_keep h G.apart (by omega) hb40 Fsw
    have fesp : (freed 16 t).gpr .esp = s.gpr .esp := by rw [freed_esp, tesp, ← hP]; exact BitVec.sub_add_cancel _ _
    refine ⟨fesp, by rw [freed_rd, Kt.2.1, wrd, K₃.2.1], by rw [freed_wr, Kt.2.2, wwr, List.tail_cons, K₃.2.2], ?_,
      by rw [freed_gpr _ _ (by decide), E, dw], ?_⟩
    · rw [freed_mem, Mt]; exact Fw
    · refine ⟨fun r hr => ?_, by rw [freed_rd, Kt.2.1, wrd, K₃.2.1], by rw [freed_wr, Kt.2.2, wwr, List.tail_cons, K₃.2.2]⟩
      have e : r = .ebx ∨ r = .esp := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        cases r <;> simp_all
      rcases e with rfl | rfl
      · rw [freed_gpr _ _ (by decide), Kt.1 _ (by decide), Kw.1 _ (by decide), K₂'.1 _ (by decide),
          K₁.1 _ (by decide), allocFrame_gpr _ _ (by decide)]
      · rw [fesp, sp₃]
  · -- `edi` back, and the width to the header.
    obtain ⟨sp₄, rd₄, wr₄, Fr₄, ea₄, K₄⟩ := H₄
    show WP isa (.block [.mov .edi (.mem (argAt 0 wsArg)), .store (sc recOff) .eax]) s₄ _
    refine wp_movS (arg_in h₃ (k := 0) (i := 16) (by decide) (by rw [sp₄, sp₃]; simp) rd₄
      (fun r hr => by rw [wr₄]; exact hr) (by rw [sp₃]; exact Fr₄)) fun s₅ U₅ _ => ?_
    have K₅ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₅ := by
      refine ⟨fun r hr => ?_, by rw [U₅.rd, rd₄, K₃.2.1], by rw [U₅.wr, wr₄, K₃.2.2]⟩
      have e : r = .edi ∨ r = .esp := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        cases r <;> simp_all
      rcases e with rfl | rfl
      · rw [U₅.gpr]; exact h.edi_eq
      · rw [U₅.other _ (by decide), sp₄]
    have Fs₅ : Frame [below (s.gpr .esp) 96] s₃.mem s₅.mem := by rw [U₅.mem]; exact Fr₄
    have F₅ : Frame (frameR base (s.gpr .esp) (fR len)) s.mem s₅.mem := F₃.trans (stk_frameR Fs₅)
    have h₅ : In Ex base bytes len args s₅ := h.keepF K₅ (by decide) (by decide) F₅ (fR_fit h)
    refine WP.mono (hdr_store h₅ (d := recOff) (by simp only [recOff]; omega) .eax) fun u ⟨I, O, W, K, _⟩ => ?_
    have sp₅ : s₅.gpr .esp = s.gpr .esp := K₅.1 _ (by decide)
    refine ⟨⟨I, F₅.trans (fR_of_outside h₅ O (.inr ⟨by simp only [recOff]; omega, by simp only [recOff]; omega⟩)),
      K₅.trans (K.mono (by decide))⟩, ?_, ?_⟩
    · exact (k₃.trans (kept_ops h₃ (sp := s.gpr .esp) (stk_frameR Fs₅) h.room).mono).trans
        (kept_word h₅ (d := recOff) (by simp only [recOff]; omega) (by decide) O).mono
    · rw [W, U₅.other _ (by decide), ea₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (recognize_lt _ _)]

end

end VG.Proof.Ffdh.X86.Cached
