module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Data
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Entry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.X86.Cached
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Search.Words
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Impl.Mont.X86

/-! # Steps of the key search (x86)

`St o ds f`: a state of the run from the entry state `o`, `esi` at the
state, whose words at the offsets `ds` hold `f`, whose memory differs from
the entry's only where the run may write. A load of a word (`St.ld`), a
store (`St.stw`), a register-only instruction (`St.reg`, `St.fupd`) and the
zeros at the outputs (`St.zeroOutputs`) keep it.
-/

@[expose] public section

/-! ## Zeros at an output (x86)

`zeroOut d` writes `p_len` zeros at the pointer in the state's word at `d`,
one byte at a time (`zeroOut_ok`), changing only `eax`, `ecx` and `edx`.
-/

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search

/-- A byte of a store of one byte. -/
theorem byte_write {m : Mem} {a x : Addr} {v : BitVec 8} : (m.writeW a v) x = if x = a then v else m x := by
  have e : (x - a).toNat < 8 / 8 ↔ x = a := by
    rw [show 8 / 8 = 1 from rfl, Nat.lt_one_iff, ← BitVec.toNat_zero (w := 64), BitVec.toNat_inj]
    constructor
    · intro h; rw [← BitVec.sub_add_cancel x a, h, BitVec.zero_add]
    · intro h; rw [h, BitVec.sub_self]
  simp only [Mem.writeW, Mem.write, e]
  split
  · next h => subst h; simp
  · rfl

/-- `mov byte [m], r`. -/
theorem wp_store8 {is : List Instr} {s : State} {Q : State → Prop} {r : Reg8} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := {s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8)})
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem Upd.keeps {s t : State} {d : Reg} {v : BitVec 32} (h : Upd s t d v) : Keeps [d] s t :=
  ⟨fun r hr => h.other r fun e => hr (e ▸ List.mem_singleton_self _), h.rd, h.wr⟩

theorem Mupd.keeps {s t : State} {m : Mem} (h : Mupd s t m) (rs : List Reg) : Keeps rs s t :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr⟩

/-- The output after `k` of its `n` bytes are zeroed. -/
structure ZInv (s₀ : State) (P : BitVec 32) (n k : Nat) (t : State) : Prop where
  edx : t.gpr .edx = P + BitVec.ofNat 32 k
  ecx : t.gpr .ecx = BitVec.ofNat 32 (n - k)
  eax : t.gpr .eax = 0
  frame : Frame [⟨P.setWidth 64, n⟩] s₀.mem t.mem
  zero : ∀ i < k, t.mem (P.setWidth 64 + BitVec.ofNat 64 i) = 0
  keeps : Keeps [.eax, .ecx, .edx] s₀ t

theorem zeroStep_ok {s₀ t : State} {P : BitVec 32} {n k : Nat} (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s₀.wr)
    (hb : P.toNat + n ≤ 2 ^ 32) (hn : n < 2 ^ 32) (hk : k < n) (I : ZInv s₀ P n k t) :
    WP isa (.block [.store8 (at_ .edx 0) .al, .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun u => ZInv s₀ P n (k + 1) u ∧ u.zf = some (decide (n - (k + 1) = 0)) := by
  have hp : t.ea (at_ .edx 0) = P.setWidth 64 + BitVec.ofNat 64 k := by
    show (t.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, I.edx]; exact addr_eq (by omega)
  have hw : InRegions t.wr (P.setWidth 64 + BitVec.ofNat 64 k) 1 :=
    ⟨_, by rw [I.keeps.2.2]; exact hR, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_store8 hp hw fun u₁ m₁ => wp_addi fun u₂ v₂ => wp_subi fun u₃ v₃ _ z₃ => WP.block_nil ?_
  have hv : (t.gpr (Reg8.al).reg).setWidth 8 = 0 := by show (t.gpr .eax).setWidth 8 = 0; rw [I.eax]; rfl
  rw [hv] at m₁
  have kk : Keeps [.eax, .ecx, .edx] t u₃ :=
    ((m₁.keeps _).trans (v₂.keeps.mono (by decide))).trans (v₃.keeps.mono (by decide))
  have mem₃ : u₃.mem = t.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  have fr : Frame [⟨P.setWidth 64, n⟩] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.keeps.trans kk⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.edx, BitVec.add_assoc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_add_ofNat]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.ecx, ofNat_pred (by omega)]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.eax]
  · rw [mem₃, byte_write]
    by_cases hik : i = k
    · subst hik; simp
    · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) hik)]
      exact I.zero i (by omega)
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.ecx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- `p_len` zeros at the pointer `P` in the state's word at `d`. -/
theorem zeroOut_ok {s : State} {S P : BitVec 32} {d n : Nat} (hesi : s.gpr .esi = S)
    (hd : InRegions (s.rd ++ s.wr) (addr S d) 4) (hl : InRegions (s.rd ++ s.wr) (addr S lenOff) 4)
    (hP : s.mem.readW (addr S d) 32 = P) (hn : s.mem.readW (addr S lenOff) 32 = BitVec.ofNat 32 n)
    (hR : (⟨P.setWidth 64, n⟩ : Region) ∈ s.wr) (h0 : 0 < n) (hb : P.toNat + n ≤ 2 ^ 32) (hn32 : n < 2 ^ 32) :
    WP isa (zeroOut d) s fun u => Frame [⟨P.setWidth 64, n⟩] s.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) n = List.replicate n 0 ∧ Keeps [.eax, .ecx, .edx] s u := by
  unfold zeroOut
  refine WP.seq (wp_ldm hesi hd fun t₁ u₁ => ?_)
  refine wp_ldm ((u₁.other _ (by decide)).trans hesi) (by rw [u₁.rd, u₁.wr]; exact hl) fun t₂ u₂ => ?_
  refine wp_movi fun t₃ u₃ => WP.block_nil ?_
  have k₃ : Keeps [.eax, .ecx, .edx] s t₃ :=
    ((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))
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

end VG.Proof.Ffdh.X86.Cached.Search

namespace VG.Proof.Ffdh.X86.Cached.Search

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.KeySearch hiding entry arguments argsBytes attempt attemptOrRequest branch iteration code
open VG.Impl.Ffdh.X86.Cached.Search
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The registers the controller uses for itself. -/
abbrev Scratch (r : Reg) : Prop := r = .eax ∨ r = .ecx ∨ r = .edx

structure St (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  abi : KeySearchABI o
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  esp : s.gpr .esp = o.gpr .esp
  esi : s.gpr .esi = arg o 12
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame (frameR o) o.mem s.mem
  words : Ctl s.mem (arg o 12) ds f

theorem saved_ne {r q : Reg} (hq : Scratch q) (hr : r ∈ calleeSaved) : r ≠ q := by
  rcases hq with rfl | rfl | rfl <;> simp [calleeSaved] at hr <;> rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem St.reg {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {r : Reg} {v : BitVec 32}
    (U : Upd s t r v) (hr : Scratch r) : St o ds f t := by
  refine ⟨h.abi, U.rd.trans h.rd, U.wr.trans h.wr, ?_, ?_, fun q hq hne => ?_, U.mem ▸ h.frame, U.mem ▸ h.words⟩
  · rw [U.other _ (saved_ne hr (by decide)), h.esp]
  · rw [U.other _ (saved_ne hr (by decide)), h.esi]
  · rw [U.other _ (saved_ne hr hq), h.saved q hq hne]

theorem St.fupd {o s t : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (F : Fupd s t) :
    St o ds f t :=
  ⟨h.abi, F.rd.trans h.rd, F.wr.trans h.wr, by rw [F.gpr, h.esp], by rw [F.gpr, h.esi],
    fun q hq hne => by rw [F.gpr, h.saved q hq hne], F.mem ▸ h.frame, F.mem ▸ h.words⟩

theorem Live.st {p : KPub} {o s : State} {used keys scalars : Nat} (h : Live p o used keys scalars s) :
    St o liveDs (liveF p (o.gpr .esi) used keys scalars) s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨A, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words⟩

theorem liveDs_aligned : Aligned liveDs := by decide

/-- The state's words are readable and writable. -/
theorem St.wIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions s.wr (addr (arg o 12) d) 4 := by
  rw [h.wr]; exact ⟨_, sR_mem h.abi, st_in h.abi hd⟩

theorem St.rIn {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) {d : Nat} (hd : d + 4 ≤ 128) :
    InRegions (s.rd ++ s.wr) (addr (arg o 12) d) 4 :=
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

/-- A store and the word it keeps. -/
theorem Ctl.write' {m : Mem} {S : BitVec 32} (hS : S.toNat + 128 ≤ 2 ^ 32) {ds : List Nat}
    {f : Nat → BitVec 32} (h : Ctl m S ds f) (hA : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0)
    (v : BitVec 32) : Ctl (m.writeW (addr S d) v) S (d :: ds) (upd f d v) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · rw [readW_write hS v hd hd (Or.inl rfl)]; simp [upd]
  · exact h.write hS hA hd hd4 v e he

theorem Aligned.cons {ds : List Nat} (h : Aligned ds) {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) :
    Aligned (d :: ds) := fun e he => by
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨hd, hd4⟩
  · exact h e he

/-- `mov [esi + d], r`. -/
theorem St.stw {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds) {r : Reg}
    {d : Nat} (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, St o (d :: ds) (upd f d (s.gpr r)) t → t.gpr = s.gpr → t.zf = s.zf → t.cf = s.cf →
      Frame [sR o] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.store (st d) r :: rest)) s Q := by
  refine wp_storeS (st_ea h.esi d) (h.wIn hd) fun t M => k t ?_ M.gpr M.zf M.cf
    (by rw [M.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (st_in h.abi hd))
  refine ⟨h.abi, M.rd.trans h.rd, M.wr.trans h.wr, by rw [M.gpr, h.esp], by rw [M.gpr, h.esi],
    fun q hq hne => by rw [M.gpr, h.saved q hq hne], ?_, ?_⟩
  · rw [M.mem]; exact h.frame.writeW (List.mem_append_left _ (sR_mem h.abi)) _ (st_in h.abi hd)
  · rw [M.mem]; exact h.words.write' h.abi.sBound hA hd hd4 _

theorem Ctl.sub {m : Mem} {S : BitVec 32} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f)
    (hs : ∀ d ∈ ds', d ∈ ds) : Ctl m S ds' f := fun d hd => h d (hs d hd)

theorem St.sub {o s : State} {ds ds' : List Nat} {f : Nat → BitVec 32} (h : St o ds f s)
    (hs : ∀ d ∈ ds', d ∈ ds) : St o ds' f s :=
  ⟨h.abi, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words.sub hs⟩

theorem St.congr {o s : State} {ds : List Nat} {f g : Nat → BitVec 32} (h : St o ds f s)
    (e : ∀ d ∈ ds, f d = g d) : St o ds g s :=
  ⟨h.abi, h.rd, h.wr, h.esp, h.esi, h.saved, h.frame, h.words.congr e⟩

/-- The outputs' regions. -/
theorem xR_eq {o : State} (A : KeySearchABI o) : xR o = ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
  rw [xR, A.xLen]
theorem yR_eq {o : State} (A : KeySearchABI o) : yR o = ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
  rw [yR, A.yLen]

/-- Zeros at the output `P` (`x` or `y`). -/
theorem St.zeroOne {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    {d : Nat} {P : BitVec 32} (hdP : f d = P) (hl : f lenOff = BitVec.ofNat 32 (arg o 7).toNat)
    (hdd : d ∈ ds) (hdl : lenOff ∈ ds) (hd4 : d + 4 ≤ 128)
    (hin : (⟨P.setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr)
    (hs : (stR (arg o 12)).Disjoint ⟨P.setWidth 64, (arg o 7).toNat⟩) (hb : P.toNat + (arg o 7).toNat ≤ 2 ^ 32) :
    WP isa (zeroOut d) s fun u => St o ds f u ∧
      Spec.Rsa.bytesAt u.mem (P.setWidth 64) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      Frame [⟨P.setWidth 64, (arg o 7).toNat⟩] s.mem u.mem ∧ (∀ r, ¬ Scratch r → u.gpr r = s.gpr r) := by
  have A := h.abi
  have hp := A.pLen
  unfold Spec.Ffdh.pLenValid at hp
  refine WP.mono (zeroOut_ok h.esi (h.rIn hd4) (h.rIn (by decide)) ((h.words.get hdd).trans hdP)
    ((h.words.get hdl).trans hl) (by rw [h.wr]; exact hin) (by omega) hb (by omega)) fun t ⟨F, Z, K⟩ => ?_
  refine ⟨⟨A, K.2.1.trans h.rd, K.2.2.trans h.wr, by rw [K.1 _ (by decide), h.esp],
      by rw [K.1 _ (by decide), h.esi], fun q hq hne => ?_, h.frame.trans (F.mono fun r hr => ?_),
      h.words.frame A.sBound hA F fun r hr => ?_⟩, Z, F, fun r hr => K.1 _ fun hm => hr (by simp at hm; omega)⟩
  · rw [K.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), h.saved q hq hne]
  · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ hin
  · simp only [List.mem_singleton] at hr; subst hr; exact hs

/-- Zeros at `x` and `y`. -/
theorem St.zeroOutputs {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : St o ds f s) (hA : Aligned ds)
    (hx : f xOff = arg o 0) (hy : f yOff = arg o 2) (hl : f lenOff = BitVec.ofNat 32 (arg o 7).toNat)
    (hdx : xOff ∈ ds) (hdy : yOff ∈ ds) (hdl : lenOff ∈ ds) :
    WP isa zeroOutputs s fun u => St o ds f u ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer o 0) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer o 2) (arg o 7).toNat = List.replicate (arg o 7).toNat 0 ∧
      u.gpr .esp = s.gpr .esp ∧ (∀ r, ¬ Scratch r → u.gpr r = s.gpr r) := by
  have A := h.abi
  have hS := A.sBound
  have hp := A.pLen
  unfold Spec.Ffdh.pLenValid at hp
  have xb : (arg o 0).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.xBound; rw [A.xLen] at this; exact this
  have yb : (arg o 2).toNat + (arg o 7).toNat ≤ 2 ^ 32 := by have := A.yBound; rw [A.yLen] at this; exact this
  have xin : (⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← xR_eq A, A.wr]; exact List.mem_cons_self ..
  have yin : (⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ : Region) ∈ o.wr := by
    rw [← yR_eq A, A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have xs : (stR (arg o 12)).Disjoint ⟨(arg o 0).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← xR_eq A]; exact A.xs.symm
  have ys : (stR (arg o 12)).Disjoint ⟨(arg o 2).setWidth 64, (arg o 7).toNat⟩ := by
    rw [← yR_eq A]; exact A.ys.symm
  refine WP.seq (WP.mono (zeroOut_ok h.esi (h.rIn (by decide)) (h.rIn (by decide)) ((h.words.get hdx).trans hx)
    ((h.words.get hdl).trans hl) (by rw [h.wr]; exact xin) (by omega) xb (by omega)) fun t ⟨F, Z, K⟩ => ?_)
  have ht : St o ds f t := by
    refine ⟨A, K.2.1.trans h.rd, K.2.2.trans h.wr, by rw [K.1 _ (by decide), h.esp],
      by rw [K.1 _ (by decide), h.esi], fun q hq hne => ?_, h.frame.trans (F.mono fun r hr => ?_),
      h.words.frame hS hA F fun r hr => ?_⟩
    · rw [K.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), h.saved q hq hne]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ xin
    · simp only [List.mem_singleton] at hr; subst hr; exact xs
  refine WP.mono (zeroOut_ok ht.esi (ht.rIn (by decide)) (ht.rIn (by decide)) ((ht.words.get hdy).trans hy)
    ((ht.words.get hdl).trans hl) (by rw [ht.wr]; exact yin) (by omega) yb (by omega)) fun u ⟨F', Z', K'⟩ => ?_
  refine ⟨⟨A, K'.2.1.trans ht.rd, K'.2.2.trans ht.wr, by rw [K'.1 _ (by decide), ht.esp],
      by rw [K'.1 _ (by decide), ht.esi], fun q hq hne => ?_, ht.frame.trans (F'.mono fun r hr => ?_),
      ht.words.frame hS hA F' fun r hr => ?_⟩, ?_, Z', ?_, fun r hr => ?_⟩
  · rw [K'.1 _ (fun hm => saved_ne (q := q) (by simp at hm; omega) hq rfl), ht.saved q hq hne]
  · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ yin
  · simp only [List.mem_singleton] at hr; subst hr; exact ys
  · rw [bytes_frame F' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [← xR_eq A, ← yR_eq A]; exact A.xy) (by omega)]
    exact Z
  · rw [K'.1 _ (by decide), K.1 _ (by decide)]
  · rw [K'.1 _ (fun hm => hr (by simp at hm; omega)), K.1 _ (fun hm => hr (by simp at hm; omega))]

end VG.Proof.Ffdh.X86.Cached.Search
