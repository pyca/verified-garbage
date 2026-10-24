module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Data
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Steps
public import VerifiedGarbage.Impl.Ffdh.X86.ParamSearch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Zero
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Steps of the parameter search (x86)

`St o ds f`: a state of the run from the entry state `o`, `esi` at the
state, whose words at the offsets `ds` hold `f`, whose memory differs from
the entry's only where the run may write. A load of a word (`St.ld`), a
store (`St.stw`), a register-only instruction (`St.reg`, `St.fupd`) and the
zeros at the output (`St.zeroOut`) keep it.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd stR contains_addr bytes_frame Scratch saved_ne ZInv zeroStep_ok)
open VG.Proof.Dsa.X86 (argumentPointer)

/-- Argument `i`'s word lies in the arguments' region. -/
theorem arg_in {o : State} (A : PSearchABI o) {i : Nat} (hi : i < 10) :
    (aR o).Contains (addr (o.gpr .esp) (4 + 4 * i)) 4 := by
  have hb := A.stackBound
  show (⟨argAddr o 0, 40⟩ : Region).Contains _ _
  rw [addr_eq (by omega), show argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 from
    addr_eq (k := 4) (by omega)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

/-- The state's word at `d` lies in the state's region. -/
theorem st_in {o : State} (A : PSearchABI o) {d : Nat} (hd : d + 4 ≤ 128) :
    (sR o).Contains (addr (arg o 9) d) 4 :=
  contains_addr A.sBound hd

theorem oR_mem {o : State} (A : PSearchABI o) : oR o ∈ o.wr := by rw [A.wr]; simp
theorem uR_mem {o : State} (A : PSearchABI o) : uR o ∈ o.wr := by rw [A.wr]; simp
theorem bR_mem {o : State} (A : PSearchABI o) : bR o ∈ o.wr := by rw [A.wr]; simp
theorem sR_mem {o : State} (A : PSearchABI o) : sR o ∈ o.wr := by rw [A.wr]; simp
theorem aR_mem {o : State} (A : PSearchABI o) : aR o ∈ o.wr := by rw [A.wr]; simp

theorem st_ea {s : State} {S : BitVec 32} (h : s.gpr .esi = S) (d : Nat) : s.ea (st d) = addr S d := by
  show s.ea ⟨.esi, d⟩ = _; rw [ea_mk, h]

structure St (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : PSearchABI o
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  syms : s.syms = o.syms
  esp : s.gpr .esp = o.gpr .esp
  esi : s.gpr .esi = arg o 9
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 9) ds f

theorem St.reg {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : Reg} {v : BitVec 32}
    (U : Upd s t r v) (hr : Scratch r) : St o ds f t := by
  refine ⟨h.abi, U.rd.trans h.rd, U.wr.trans h.wr, U.syms.trans h.syms, ?_, ?_, fun q hq hne => ?_,
    U.mem ▸ h.frame, U.mem ▸ h.words⟩
  · rw [U.other _ (saved_ne hr (by decide)), h.esp]
  · rw [U.other _ (saved_ne hr (by decide)), h.esi]
  · rw [U.other _ (saved_ne hr hq), h.saved q hq hne]

theorem St.fupd {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (F : Fupd s t) :
    St o ds f t :=
  ⟨h.abi, F.rd.trans h.rd, F.wr.trans h.wr, F.syms.trans h.syms, by rw [F.gpr, h.esp], by rw [F.gpr, h.esi],
    fun q hq hne => by rw [F.gpr, h.saved q hq hne], F.mem ▸ h.frame, F.mem ▸ h.words⟩

theorem Live.st {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) :
    St o liveDs (liveF p (o.gpr .esi) used n) s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨A, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words⟩

theorem liveDs_aligned : Aligned liveDs := by decide

/-- The state's words are readable and writable. -/
theorem St.wIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions s.wr (addr (arg o 9) d) 4 := by
  rw [h.wr]; exact ⟨_, sR_mem h.abi, st_in h.abi hd⟩

theorem St.rIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions (s.rd ++ s.wr) (addr (arg o 9) d) 4 :=
  let ⟨r, hr, hc⟩ := h.wIn hd; ⟨r, List.mem_append_right _ hr, hc⟩

/-- `mov r, [esi + d]`. -/
theorem St.ld {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : Reg} (hr : Scratch r)
    {d : Nat} (hd : d ∈ ds) (hd4 : d + 4 ≤ 128) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o ds f t → t.gpr r = f d → (∀ q, q ≠ r → t.gpr q = s.gpr q) → t.cf = s.cf →
      t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.mov r (.mem (st d)) :: rest)) s Q := by
  show WP isa (.block (.mov r (.mem ⟨.esi, d⟩) :: rest)) s Q
  refine wp_movS (readSrc_mem h.esi (h.rIn hd4)) fun t U c => k t (h.reg U hr) ?_ U.other c U.mem
  rw [U.gpr]; exact h.words.get hd

/-- `mov [esi + d], r`. -/
theorem St.stw {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds) {r : Reg}
    {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o (d :: ds) (upd f d (s.gpr r)) t → t.gpr = s.gpr → t.zf = s.zf → t.cf = s.cf →
      Frame [sR o] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.store (st d) r :: rest)) s Q := by
  refine wp_storeS (st_ea h.esi d) (h.wIn hd) fun t M => k t ?_ M.gpr M.zf M.cf
    (by rw [M.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (st_in h.abi hd))
  refine ⟨h.abi, M.rd.trans h.rd, M.wr.trans h.wr, M.syms.trans h.syms, by rw [M.gpr, h.esp],
    by rw [M.gpr, h.esi], fun q hq hne => by rw [M.gpr, h.saved q hq hne], ?_, ?_⟩
  · rw [M.mem]; exact h.frame.writeW (List.mem_append_left _ (sR_mem h.abi)) _ (st_in h.abi hd)
  · rw [M.mem]; exact h.words.write' h.abi.sBound hA hd hd4 _

theorem St.sub {o s : State} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : St o ds f s)
    (hs : ∀ d ∈ ds', d ∈ ds) : St o ds' f s :=
  ⟨h.abi, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words.sub hs⟩

theorem St.congr {o s : State} {ds : List Nat} {f g : Nat → BitVec 32} (h : St o ds f s)
    (e : ∀ d ∈ ds, f d = g d) : St o ds g s :=
  ⟨h.abi, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words.congr e⟩

/-- The output's region. -/
theorem oR_eq {o : State} : oR o = ⟨(arg o 0).setWidth 64, (arg o 1).toNat⟩ := rfl

theorem len_pos {o : State} (A : PSearchABI o) : 64 ≤ (arg o 1).toNat ∧ (arg o 1).toNat ≤ 1024 := by
  have := A.outLen
  have := A.bitsLow
  have := A.bitsHigh
  omega

/-- Zeros at the output, the width's octets. -/
theorem zeroOut_ok {s : State} {S P : BitVec 32} {n : Nat} (hesi : s.gpr .esi = S)
    (hd : InRegions (s.rd ++ s.wr) (addr S outOff) 4) (hl : InRegions (s.rd ++ s.wr) (addr S widthOff) 4)
    (hP : s.mem.readW (addr S outOff) 32 = P) (hn : s.mem.readW (addr S widthOff) 32 = BitVec.ofNat 32 n)
    (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s.wr) (h0 : 0 < n) (hb : P.toNat + n ≤ 2 ^ 32) (hn32 : n < 2 ^ 32) :
    WP isa zeroOut s fun u => Frame [⟨P.setWidth 64, n⟩] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) n = List.replicate n 0 ∧ Keeps [.eax, .ecx, .edx] s u := by
  unfold zeroOut
  refine WP.seq (wp_ldm hesi hd fun t₁ u₁ => ?_)
  refine wp_ldm ((u₁.other _ (by decide)).trans hesi) (by rw [u₁.rd, u₁.wr]; exact hl) fun t₂ u₂ => ?_
  refine wp_movi fun t₃ u₃ => WP.block_nil ?_
  have k₃ : Keeps [.eax, .ecx, .edx] s t₃ :=
    ((KeySearch.Upd.keeps u₁ |>.mono (by decide)).trans (KeySearch.Upd.keeps u₂ |>.mono (by decide))).trans
      (KeySearch.Upd.keeps u₃ |>.mono (by decide))
  have m₃ : t₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have I₀ : ZInv s P n 0 t₃ := ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hP, BitVec.add_zero],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, hn, Nat.sub_zero],
    u₃.gpr, by rw [m₃]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), k₃⟩
  refine WP.loop (M := isa) (fun (j : Nat) (u : State) => ∃ k, j = n - k ∧ k < n ∧ ZInv s P n k u)
    (fun j u hu => ?_) _ t₃ ⟨0, rfl, h0, I₀⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok hR hb hn32 hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : n - (k + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], J.frame, ?_, J.keeps⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero i (by omega)
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false], _, by omega,
      k + 1, rfl, by omega, J⟩

/-- Zeros at the output. -/
theorem St.zeroOut {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (ho : f outOff = arg o 0) (hl : f widthOff = BitVec.ofNat 32 (arg o 1).toNat)
    (hdo : outOff ∈ ds) (hdl : widthOff ∈ ds) :
    WP isa zeroOut s fun u => St o ds f u ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer o 0) (arg o 1).toNat = List.replicate (arg o 1).toNat 0 ∧
      Frame [oR o] s.mem u.mem ∧ (∀ r, ¬ Scratch r → u.gpr r = s.gpr r) := by
  have A := h.abi
  have hp := len_pos A
  have ob := A.oBound
  refine WP.mono_syms (zeroOut_ok h.esi (h.rIn (by decide)) (h.rIn (by decide))
    ((h.words.get hdo).trans ho) ((h.words.get hdl).trans hl) (by rw [h.wr]; exact oR_mem A) (by omega) ob
    (by omega)) fun t ⟨F, Z, K⟩ sy => ?_
  refine ⟨⟨A, K.2.1.trans h.rd, K.2.2.trans h.wr, sy.trans h.syms, by rw [K.1 _ (by decide), h.esp],
      by rw [K.1 _ (by decide), h.esi], fun q hq hne => ?_, h.frame.trans (F.mono fun r hr => ?_),
      h.words.frame A.sBound hA F fun r hr => ?_⟩, Z, F, fun r hr => K.1 _ fun hm => hr (by simp at hm; omega)⟩
  · rw [K.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), h.saved q hq hne]
  · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ (oR_mem A)
  · simp only [List.mem_singleton] at hr; subst hr; exact A.os.symm

end VG.Proof.Ffdh.X86.PSearch
