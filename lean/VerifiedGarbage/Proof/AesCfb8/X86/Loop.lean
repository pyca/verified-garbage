import VerifiedGarbage.Proof.AesCfb8.Mem
import VerifiedGarbage.Proof.AesCbc.X86.Loop
import VerifiedGarbage.Impl.AesCfb8.X86

/-!
# AES-CFB8 on x86: the contracts, and the loop

The artifacts' contracts are the shared ones of `Spec/Cfb8/Contract.lean`,
which imply these (`Verified.lean`): `cfb8X86 enc`, for encryption
(`enc = true`) and decryption. The functions have AES-CBC's arguments, with
`len` counting bytes, and its prologue and epilogue
(`Proof/AesCbc/X86/Loop.lean`), whose stride-free definitions this reuses.

The invariant after `k` bytes (`LInv`): `esi` points at the next byte,
`esp` is unchanged, only the input block, the data, the first 2064 bytes of
the scratch buffer and the 24 bytes below `esp` have changed since the
registers were saved, the first `k` bytes are CFB8's of the first `k` bytes
on entry and the rest are unchanged, and the input block is the one after
them. Everything else is reloaded from the stack arguments, which nothing
writes.

`whole_wp`: if one run of `body` takes the invariant from `k` to `k + 1`
bytes and sets ZF when none are left (`BodyOk`), `whole body` meets the
contract.
-/

namespace VG.Proof.AesCfb8.X86

open VG VG.X86 VG.Impl.AesCbc.X86
open VG.Impl.CmacAes.X86 (argOp setup restore saved)
open VG.Proof.CmacAes.X86 (wp_arg wp_addArg saved_fits saved_bound saved_ne_eax restore_eq
  setup_eq ofNat_and_self_beq arg_ofNat add0 add0')
open VG.Proof.MdStream.X86 (Upd wp_addi wp_add wp_cmp wp_test eval_e eval_ne)
open VG.Proof.AesCbc.X86 (E W R Iv Dp N S schR ivR scrR argsR retR stkR iv0 wK savedMem savedMem_frame
  savedMem_slot savedMem_big)
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt` `(schedule, rounds, iv, data, len, scratch)`. -/
def cfb8X86 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧
      data.Disjoint scr ∧ args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint scr ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (arg s 1).toNat
      (bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1)))
    let iv := bytesAt s.mem ((arg s 2).setWidth 64) 16
    let xs := bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
    bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem ((arg s 2).setWidth 64) 16 = inK enc ciph iv xs
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

section
variable (s₀ : State)

abbrev dataR : Region := ⟨(Dp s₀).setWidth 64, N s₀⟩

/-- The cipher. -/
abbrev ciph : Spec.Cbc.Cipher := Spec.Cbc.aesWith (R s₀) (wK s₀)

/-- The bytes on entry. -/
abbrev bs : List Byte := bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)

/-- The address of byte `k`. -/
abbrev byt (k : Nat) : Addr := (Dp s₀).setWidth 64 + BitVec.ofNat 64 k

/-- The first `k` bytes after CFB8. -/
abbrev outK (enc : Bool) (k : Nat) : List Byte := cfb8 enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

/-- The input block after the first `k` bytes. -/
abbrev inKk (enc : Bool) (k : Nat) : List Byte := inK enc (ciph s₀) (iv0 s₀) ((bs s₀).take k)

end

/-- The precondition, by name. -/
structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [schR s₀, argsR s₀]
  wr : s₀.wr = [ivR s₀, dataR s₀, scrR s₀]
  sch_iv : (schR s₀).Disjoint (ivR s₀)
  sch_data : (schR s₀).Disjoint (dataR s₀)
  sch_scr : (schR s₀).Disjoint (scrR s₀)
  iv_data : (ivR s₀).Disjoint (dataR s₀)
  iv_scr : (ivR s₀).Disjoint (scrR s₀)
  data_scr : (dataR s₀).Disjoint (scrR s₀)
  args_iv : (argsR s₀).Disjoint (ivR s₀)
  args_data : (argsR s₀).Disjoint (dataR s₀)
  args_scr : (argsR s₀).Disjoint (scrR s₀)
  ret_iv : (retR s₀).Disjoint (ivR s₀)
  ret_data : (retR s₀).Disjoint (dataR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  b_sch : (stkR s₀).Disjoint (schR s₀)
  b_iv : (stkR s₀).Disjoint (ivR s₀)
  b_data : (stkR s₀).Disjoint (dataR s₀)
  b_scr : (stkR s₀).Disjoint (scrR s₀)
  sch_fit : (W s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (Iv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (Dp s₀).toNat + N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  esp24 : 24 ≤ (E s₀).toNat
  esp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14

theorem UPre.of {enc : Bool} {s₀ : State} (h : (cfb8X86 enc).pre s₀) : UPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z⟩

/-- The loop invariant, after `k` bytes. -/
structure LInv (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 k
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s.mem
  data : bytesAt s.mem ((Dp s₀).setWidth 64) (N s₀) = outK s₀ enc k ++ (bs s₀).drop k
  iv : bytesAt s.mem ((Iv s₀).setWidth 64) 16 = inKk s₀ enc k

/-! ## Addresses and regions -/

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [ivR s₀, dataR s₀, scrR s₀, stkR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.below_eq : below (E s₀) 24 = stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp24]

theorem UPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem UPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem UPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem UPre.args_stk : (argsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem UPre.arg_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.args_iv.sub_left (hp.arg_sub hi)
    · exact hp.args_data.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem UPre.dataA {k : Nat} (hk : k < N s₀) : addr (Dp s₀) k = byt s₀ k :=
  addr_eq (by have := hp.data_fit; omega)

theorem UPre.dataN {k : Nat} (hk : k < N s₀) : (Dp s₀ + BitVec.ofNat 32 k).toNat = (Dp s₀).toNat + k := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem UPre.byt_disjoint {j k : Nat} (hj : j < N s₀) (hk : k < N s₀) (hjk : j ≠ k) :
    (⟨byt s₀ j, 1⟩ : Region).Disjoint ⟨byt s₀ k, 1⟩ := by
  have := hp.data_fit
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

end

theorem UPre.scr_sub {s₀ : State} {d n : Nat} (h : d + n ≤ 2176) :
    Region.Sub ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

theorem UPre.data_sub {s₀ : State} {k : Nat} (hk : k < N s₀) : Region.Sub ⟨byt s₀ k, 1⟩ (dataR s₀) :=
  Offset.sub_base _ (by omega)

theorem UPre.big_of {s₀ : State} {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m :=
  ((savedMem_frame s₀).mono (by simp)).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    bytesAt m ((W s₀).setWidth 64) (16 * (R s₀ + 1)) = bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left (Region.sub_prefix hR)
  · exact hp.sch_data.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

/-- The bytes after a step that changed only byte `k`, the input block, the
first 2064 bytes of the scratch buffer and the stack. -/
theorem UPre.bytes_step {m m' : Mem} {k : Nat} (hk : k < N s₀)
    (hf : Frame [⟨byt s₀ k, 1⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] m m') :
    bytesAt m' ((Dp s₀).setWidth 64) (N s₀) =
      (bytesAt m ((Dp s₀).setWidth 64) (N s₀)).set k (m' (byt s₀ k)) := by
  refine bytesAt_set fun j hj hjk => ?_
  have e := Proof.Cmac.bytesAt_frame (p := byt s₀ j) (n := 1) hf (fun r hr => ?_) (by decide)
  · simpa [bytesAt] using e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.byt_disjoint hj hk hjk
  · exact hp.iv_data.symm.sub_left (UPre.data_sub hj)
  · exact (hp.data_scr.sub_left (UPre.data_sub hj)).sub_right (Region.sub_prefix (by decide))
  · exact hp.b_data.symm.sub_left (UPre.data_sub hj)

end

theorem length_bs (s₀ : State) : (bs s₀).length = N s₀ := by simp [bytesAt]

/-- Byte `k` before the step, from the invariant. -/
theorem LInv.byte {enc : Bool} {s₀ : State} {k : Nat} {s : State} (h : LInv enc s₀ k s) (hk : k < N s₀) :
    s.mem (byt s₀ k) = (bs s₀)[k]'(by rw [length_bs]; exact hk) := by
  have hl : (outK s₀ enc k).length = k := by
    rw [outK, length_cfb8, List.length_take, length_bs]; omega
  have := congrArg (·[k]?) h.data
  simp only [List.getElem?_append_right (show (outK s₀ enc k).length ≤ k by omega), hl, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero] at this
  rw [List.getElem?_eq_getElem (by simp [bytesAt]; exact hk),
    List.getElem?_eq_getElem (by rw [length_bs]; exact hk)] at this
  simpa [bytesAt] using Option.some.inj this

theorem take_succ_bs (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (bs s₀).take (k + 1) = (bs s₀).take k ++ [(bs s₀)[k]'(by rw [length_bs]; exact hk)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [length_bs]; exact hk)]
  rfl

/-! ## The prologue -/

theorem prologue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) :
    WP isa (.block setup) s₀ fun s => LInv enc s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)) := by
  have hsc := hp.scr_fit
  rw [setup_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = savedMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  have sb : Frame (Big s₀) s₀.mem (savedMem s₀) := (savedMem_frame s₀).mono (by simp)
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact hp.arg_keep sb (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep sb (by decide)) fun s₄ u₄ => ?_
  have f₀ := savedMem_frame s₀
  have ivS : bytesAt (savedMem s₀) ((Iv s₀).setWidth 64) 16 = iv0 s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_scr) (by decide)
  have dataS : bytesAt (savedMem s₀) ((Dp s₀).setWidth 64) (N s₀) = bs s₀ :=
    Proof.Cmac.bytesAt_frame f₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_scr) (by have := hp.data_fit; omega)
  refine wp_test fun s₅ f₅ z₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, add0']
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]; exact Frame.refl _ _
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, dataS]
    simp only [outK, List.take_zero, cfb8_nil, List.drop_zero, List.nil_append]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂, ivS]
    simp only [inKk, List.take_zero, inK_nil]
  · rw [z₅, u₄.gpr, arg_ofNat s₀ 4, ofNat_and_self_beq (arg s₀ 4).isLt]

/-! ## The end of a byte -/

theorem advance_eq : Impl.AesCfb8.X86.advance = .alu .add .esi (.imm 1) :: .mov .eax (argOp 4) ::
    .alu .add .eax (argOp 3) :: .alu .cmp .esi (.reg .eax) :: [] := rfl

theorem adv_zf {D n : BitVec 32} {k : Nat} (hk : k < n.toNat) (_hfit : D.toNat + n.toNat ≤ 2 ^ 32) :
    (D + BitVec.ofNat 32 k + 1 - (n + D) == 0) = decide (k + 1 = n.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  have := D.isLt
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  omega

theorem advance_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (hesi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 k) (hesp : s.gpr .esp = E s₀)
    (hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) :
    WP isa (.block Impl.AesCfb8.X86.advance) s fun s' => s'.gpr .esi = Dp s₀ + BitVec.ofNat 32 (k + 1) ∧
      s'.gpr .esp = E s₀ ∧ (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  rw [advance_eq]
  refine wp_addi fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 4 (by decide)) fun s₂ u₂ => ?_
  refine wp_addArg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact hargs 3 (by decide)) fun s₃ u₃ => ?_
  refine wp_cmp fun s₄ f₄ _ z₄ => WP.block_nil ⟨?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hesi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add_eq _ (c := k + 1) (by omega)]
  · rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp]
  · rw [f₄.gpr, u₃.other _ h₁, u₂.other _ h₁, u₁.other _ h₂]
  · rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [z₄, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, hesi]
    exact congrArg some (adv_zf hk hp.data_fit)

/-! ## The loop -/

/-- One run of `body` takes the invariant from `k` bytes to `k + 1`, and sets
ZF if no bytes are left. -/
def BodyOk (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
    WP isa body s fun s' => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀))

theorem loop_ok {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LInv enc s₀ k s) : WP isa (.loop body .ne) s (LInv enc s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv enc s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv enc s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (hb hp hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

theorem mid_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {s₁ : State}
    (h : LInv enc s₀ 0 s₁) (hz : s₁.zf = some (decide (N s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop body .ne)) s₁ (LInv enc s₀ (N s₀)) := by
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, hz]
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev]; simp [hn]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact h
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hb hp (by omega) h

/-! ## The epilogue -/

theorem slot_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) {d : Nat}
    (h₁ : 2064 ≤ d) (h₂ : d + 4 ≤ 2080) :
    m.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 =
      (savedMem s₀).readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 :=
  hf.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact hp.data_scr.symm.sub_left (UPre.scr_sub (by omega))
    · exact Offset.disjoint_base _ h₁ (by omega)
    · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide)

theorem UPre.ret_stk {s₀ : State} (_hp : UPre s₀) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 24) (a := 0) (l := 4) (by decide)
  rw [add0] at this
  exact this.symm

/-- The return address, which nothing writes. -/
theorem ret_read {s₀ : State} (hp : UPre s₀) {m : Mem}
    (hf : Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) :
    m.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  (UPre.big_of hf).readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact hp.ret_stk) (by decide)

theorem epilogue_wp {enc : Bool} {s₀ : State} (hp : UPre s₀) {s : State} (h : LInv enc s₀ (N s₀) s) :
    WP isa (.block (restore 5)) s fun s' => abiPreserved s₀ s' ∧ (cfb8X86 enc).post s₀ s' := by
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have rdwr : s.rd ++ s.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
    fun r d hrd => by
      have hb := saved_bound _ hrd
      rw [slot_read hp h.frame hb.1 hb.2, savedMem_slot s₀ hrd]
  have hall : (bs s₀).take (N s₀) = bs s₀ := List.take_of_length_le (by rw [length_bs])
  have hnil : (bs s₀).drop (N s₀) = [] := List.drop_of_length_le (by rw [length_bs])
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide))
    (hp.arg_keep (UPre.big_of h.frame) (by decide)) fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok saved saved_fits (by rw [u₁.gpr]; omega) saved_ne_eax (fun p hp' => ?_)
    (fun p hp' => by rw [u₁.gpr, u₁.mem]; exact sl p.1 p.2 hp') fun s₂ r₂ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, rdwr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_, ?_⟩
  · rw [r₂.mem, u₁.mem]; exact ret_read hp h.frame
  · show bytesAt s₂.mem ((Dp s₀).setWidth 64) (N s₀) = _
    rw [r₂.mem, u₁.mem, h.data]; simp only [outK, hall, hnil, List.append_nil]
  · show bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 = _
    rw [r₂.mem, u₁.mem, h.iv]; simp only [inKk, hall]

theorem whole_wp {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (h0 : (cfb8X86 enc).pre s₀) :
    WP isa (whole body) s₀ fun s' => abiPreserved s₀ s' ∧ (cfb8X86 enc).post s₀ s' := by
  have hp := UPre.of h0
  exact WP.seq (WP.mono (prologue_wp hp) fun s₁ ⟨h₁, hz⟩ =>
    WP.seq (WP.mono (mid_wp hb hp h₁ hz) fun _ h₂ => epilogue_wp hp h₂))

end VG.Proof.AesCfb8.X86
