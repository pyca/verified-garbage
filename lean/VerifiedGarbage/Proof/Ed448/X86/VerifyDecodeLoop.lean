import VerifiedGarbage.Proof.Ed448.X86.VerifyDecode
import VerifiedGarbage.Proof.Ed448.X86.ScalarIO

/-!
# Ed448 verification's equation on x86 (32-bit): `R` and `A` decoded by one loop

`vdecode` decodes `R` (the signature's first half) and then `A` (the public key) with one copy
of the decoding: the pointer to the point it decodes next and the decodings left are words of
the working space (`PCUR`, `CNT`), and each iteration first copies slots 6–7 to `RX` and `RY`,
so that `R`, decoded into slots 6–7 by the first iteration, is kept there while `A` is decoded
into them by the second. `DecInv` is the state after `2 - m` decodings, `m` the count.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Impl.Ed448 VG.Impl.Ed448.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk)
open VG.Impl.X448.X86 (slot ACC at_ ld st sc copy)
open VG.Spec.Ed448 (bytesAt)

/-- What the loop writes: the slots, `BAD` and `SIGN` (from byte 16), and from `ACC` to `CNT`
(`R`'s place and the loop's pointer and count). -/
abbrev DFrame (base : Addr) (m m' : Mem) : Prop := Outside2 base 16 2864 ACC 776 m m'

theorem DFrame.of_v {base : Addr} {m m' : Mem} (h : Outside2 base 16 2864 ACC 512 m m') :
    DFrame base m m' :=
  fun p h1 h2 => h p h1 (by simp only [ACC] at h2 ⊢; omega)

theorem DFrame.of_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : ACC ≤ o)
    (h2 : o + n ≤ ACC + 776) : DFrame base m m' :=
  fun p _ hq => h p (by simp only [ACC] at h1 h2 hq; omega)

theorem DFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : DFrame base m₁ m₂) (h₂ : DFrame base m₂ m₃) :
    DFrame base m₁ m₃ := Outside2.trans h₁ h₂

/-- A slot's value outside a range written. -/
theorem E_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Index)
    (hi : slot i.val + 112 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  simp only [E, F]
  rw [h.fe hi (by have := slot_range i; omega)]

/-- Bounded slots outside a range written above them. -/
theorem BoundedEnv.out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (ho : 2880 ≤ o)
    (hb : BoundedEnv m base) : BoundedEnv m' base := fun i j hj => by
  have := slot_range i
  rw [h.limbs (Or.inl (by omega)) (by omega) hj]
  exact hb i j hj

/-- One store, keeping the flags. -/
theorem storeZ_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat} (hd : d + 4 ≤ 8192) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.zf = s.zf :=
  WP.cons (t := {s with mem := s.mem.writeW (off base d) (s.gpr r)})
    (by simp only [st, exec, hs.ea (by omega : d < 8192), State.store32, hs.write hd, ite_true])
    (WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- The argument at `[esp + d]`, `p`, in any later state with the same stack pointer and
regions and the memory outside the working space unchanged. -/
def ArgAt (s : State) (base : Addr) (d : Nat) (p : BitVec 32) : Prop :=
  ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd = s.rd → t.wr = s.wr → Outside base 0 8192 s.mem t.mem →
    ∃ a, t.ea (at_ .esp d) = a ∧ InRegions (t.rd ++ t.wr) a 4 ∧ t.mem.readW a 32 = p

theorem ArgAt.of {s u : State} {base : Addr} {d : Nat} {p : BitVec 32} (h : ArgAt s base d p) {rs : List Reg}
    (hk : Keeps rs s u) (hesp : .esp ∉ rs) (ho : Outside base 0 8192 s.mem u.mem) : ArgAt u base d p :=
  fun t h1 h2 h3 h4 => h t (h1.trans (hk.1 _ hesp)) (h2.trans hk.2.1) (h3.trans hk.2.2) (ho.trans h4)

/-- `decodePoint` of the 57 bytes at `p`. -/
abbrev decAt (m : Mem) (p : BitVec 32) : Option Spec.Ed448.Point :=
  Spec.Ed448.decodePoint (bytesAt m (p.setWidth 64) 57)

/-- After `2 - m` of the decodings, from the state `s` before the loop: `R`'s decoding (at `sig`)
in slots 6–7 after the first, then at `RX` and `RY` with `A`'s (at `pk`) in slots 6–7. -/
structure DecInv (base : Addr) (s : State) (sig pk : BitVec 32) (m : Nat) (t : State) : Prop where
  le : m ≤ 2
  keeps : Keeps (.esi :: workRegs) s t
  frame : DFrame base s.mem t.mem
  bounded : BoundedEnv t.mem base
  cnt : word t.mem base CNT = BitVec.ofNat 32 m
  ptr : 1 ≤ m → word t.mem base PCUR = if m = 2 then sig else pk
  other : ∀ i : Index, i ≠ 6 → i ≠ 7 → (i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11)) →
    E t.mem base i = E s.mem base i
  bad : BadUpd ((m ≤ 1 → (decAt s.mem sig).isSome) ∧ (m = 0 → (decAt s.mem pk).isSome))
    (word s.mem base BAD) (word t.mem base BAD)
  rIn : m = 1 → ∀ r, decAt s.mem sig = some r → E t.mem base 6 = r.X ∧ E t.mem base 7 = r.Y ∧ r.Z = 1
  rOut : m = 0 → ∀ r, decAt s.mem sig = some r → F t.mem base RX = r.X ∧ F t.mem base RY = r.Y ∧ r.Z = 1
  rBnd : m = 0 → Bounded t.mem base RX ∧ Bounded t.mem base RY
  aIn : m = 0 → ∀ a, decAt s.mem pk = some a → E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1

theorem DecInv.scr {base : Addr} {s t : State} {sig pk : BitVec 32} {m : Nat} (h : DecInv base s sig pk m t)
    (hs : Scr s base) : Scr t base := hs.of_keeps h.keeps (by decide)

/-- The loop's pointer at `R`, and its count 2. -/
theorem vdecodeInit_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sig pk : BitVec 32} (hsig : ArgAt s base 8 sig) :
    WP isa (.block vdecodeInit) s (DecInv base s sig pk 2) := by
  unfold vdecodeInit
  obtain ⟨a, ae, ar, av⟩ := hsig s rfl rfl rfl (Outside.refl _ _ _ _)
  refine wp_load ae ar fun u1 h1 => ?_
  rw [av] at h1
  have hs1 := hs.of_upd h1 (by decide)
  refine store_ok hs1 (o := PCUR) (by decide) fun u2 h2 => ?_
  have hs2 := hs1.of_keeps (h2.rest []) (by decide)
  refine wp_mov (v := 2) rfl fun u3 h3 => ?_
  have hs3 := hs2.of_upd h3 (by decide)
  refine store_ok hs3 (o := CNT) (by decide) fun t ht => WP.block_nil ?_
  have mt : t.mem = (s.mem.writeW (off base PCUR) sig).writeW (off base CNT) (2 : BitVec 32) := by
    rw [ht.mem, h3.gpr, h3.mem, h2.mem, h1.gpr, h1.mem]
  have out : Outside base PCUR 8 s.mem t.mem := by
    rw [mt]
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  have bt : word t.mem base BAD = word s.mem base BAD := out.word (Or.inl (by decide)) (by decide)
  refine ⟨by decide, ((h1.rest (by decide)).trans (h2.rest _)).trans ((h3.rest (by decide)).trans (ht.rest _)),
    DFrame.of_out out (by decide) (by decide), BoundedEnv.out out (by decide) hb, ?_, fun _ => ?_,
    fun i _ _ _ => E_out out i (Or.inl (by have := slot_range i; simp only [PCUR]; omega)),
    (BadUpd.rfl'.congr ⟨fun _ => ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
      fun _ => trivial⟩).of_eq bt, fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · rw [mt, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
    rfl
  · rw [mt, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl, ite_eq_left rfl]

/-- What the first block of an iteration does: slots 6–7 copied to `RX` and `RY`, and `esi`
loaded from `PCUR`. -/
def AFacts (base : Addr) (t u : State) : Prop :=
  u.gpr .esi = word t.mem base PCUR ∧ Keeps (.esi :: workRegs) t u ∧ Outside base RX 256 t.mem u.mem ∧
    (∀ i < 28, limbs u.mem base RX i = limbs t.mem base (slot 6) i) ∧
    (∀ i < 28, limbs u.mem base RY i = limbs t.mem base (slot 7) i)

theorem vbodyA_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block vbodyA) s (AFacts base s) := by
  rw [vbodyA, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok hs (o := RX) (a := slot 6) (by decide) (by decide) (Or.inr (Or.inr (by decide))))
    fun s1 ⟨f1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copy_ok hs1 (o := RY) (a := slot 7) (by decide) (by decide) (Or.inr (Or.inr (by decide))))
    fun s2 ⟨f2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  refine load_ok hs2 (o := PCUR) (by decide) fun t ht => WP.block_nil ⟨?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [ht.gpr, o2.word (Or.inr (by decide)) (by decide), o1.word (Or.inr (by decide)) (by decide)]
  · refine ((k1.mono ?_).trans (k2.mono ?_)).trans (ht.rest (by decide)) <;> intro r hr <;> revert r <;> decide
  · rw [ht.mem]
    exact (o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))
  · rw [ht.mem, o2.limbs (Or.inl (by decide)) (by decide) hi, f1 i hi]
  · rw [ht.mem, f2 i hi, o1.limbs (Or.inl (by decide)) (by decide) hi]

/-- A decoding of the point at `esi` into slots 6–7, then `vnext`. -/
theorem vdecodeRest_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base)
    (hb : BoundedEnv s.mem base) {p pk : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 57)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) (hpk : ArgAt s base 4 pk)
    {c : Nat} (hc2 : c < 2) (hc : word s.mem base CNT = BitVec.ofNat 32 (c + 1)) :
    WP isa (.seq (decode 6 7) (.block vnext)) s fun t =>
      Keeps (.esi :: workRegs) s t ∧ DFrame base s.mem t.mem ∧ BoundedEnv t.mem base ∧
      BadUpd (decAt s.mem p).isSome (word s.mem base BAD) (word t.mem base BAD) ∧
      (∀ a, decAt s.mem p = some a → E t.mem base 6 = a.X ∧ E t.mem base 7 = a.Y ∧ a.Z = 1) ∧
      (∀ i : Index, i ≠ 6 → i ≠ 7 → (i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11)) →
        E t.mem base i = E s.mem base i) ∧
      (∀ i < 28, limbs t.mem base RX i = limbs s.mem base RX i) ∧
      (∀ i < 28, limbs t.mem base RY i = limbs s.mem base RY i) ∧
      word t.mem base PCUR = pk ∧ word t.mem base CNT = BitVec.ofNat 32 c ∧ t.zf = some (decide (c = 0)) := by
  refine WP.seq (WP.mono (decode_ok hR hs hb hp hin.fit hin.read hin.far 6 7 (Or.inl ⟨rfl, rfl⟩) h10 h11)
    fun w ⟨kw, bw, cw, vw, ew⟩ => ?_)
  have hsw := kw.scr hs
  obtain ⟨a, ae, ar, av⟩ := hpk w (kw.regs.1 _ (by decide)) kw.regs.2.1 kw.regs.2.2
    (kw.mem.whole (by decide) (by decide))
  unfold vnext
  refine wp_load ae ar fun w1 g1 => ?_
  rw [av] at g1
  have hs1 := hsw.of_upd g1 (by decide)
  refine store_ok hs1 (o := PCUR) (by decide) fun w2 g2 => ?_
  have hs2 := hs1.of_keeps (g2.rest []) (by decide)
  refine load_ok hs2 (o := CNT) (by decide) fun w3 g3 => ?_
  have hs3 := hs2.of_upd g3 (by decide)
  refine wp_alu (op := .sub) (v := 1) (Or.inr (Or.inl rfl)) rfl fun w4 g4 z4 => ?_
  have hs4 := hs3.of_upd g4 (by decide)
  refine WP.mono (storeZ_ok hs4 .ebx (d := CNT) (by decide)) fun t ⟨mt, gt, rdt, wrt, zt⟩ => ?_
  have c3 : w3.gpr .ebx = BitVec.ofNat 32 (c + 1) := by
    rw [g3.gpr, g2.mem, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), g1.mem, kw.mem.word (Or.inr (by decide)) (Or.inr (by decide)) (by decide), hc]
  have c4 : w4.gpr .ebx = BitVec.ofNat 32 c := by
    rw [g4.gpr]
    show w3.gpr .ebx - 1 = _
    rw [c3]
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> rfl
  have mt' : t.mem = (w.mem.writeW (off base PCUR) pk).writeW (off base CNT) (BitVec.ofNat 32 c) := by
    rw [mt, c4, g4.mem, g3.mem, g2.mem, g1.gpr, g1.mem]
  have out : Outside base PCUR 8 w.mem t.mem := by
    rw [mt']
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  have wl : ∀ o, ACC + 512 ≤ o → o + 112 ≤ PCUR → ∀ i < 28, limbs t.mem base o i = limbs s.mem base o i :=
    fun o h1 h2 i hi => by
      rw [out.limbs (Or.inl h2) (by simp only [PCUR] at h2; omega) hi]
      exact congrArg BitVec.toNat (kw.mem.word (Or.inr (by simp only [ACC] at h1; omega))
        (Or.inr (by omega)) (by simp only [PCUR] at h2; omega))
  refine ⟨?_, (DFrame.of_v kw.mem).trans (DFrame.of_out out (by decide) (by decide)),
    BoundedEnv.out out (by decide) bw, cw.of_eq (out.word (Or.inl (by decide)) (by decide)), fun a ha => ?_,
    fun i h6 h7 hi => ?_, wl RX (by decide) (by decide), wl RY (by decide) (by decide), ?_, ?_, ?_⟩
  · refine kw.regs.trans (((g1.rest (by decide)).trans (g2.rest _)).trans (((g3.rest (by decide)).trans
      (g4.rest (by decide))).trans ⟨fun r _ => by rw [gt], rdt, wrt⟩))
  · obtain ⟨x, y, z⟩ := vw a ha
    exact ⟨by rw [E_out out 6 (Or.inl (by decide))]; exact x, by rw [E_out out 7 (Or.inl (by decide))]; exact y, z⟩
  · rw [E_out out i (Or.inl (by have := slot_range i; simp only [PCUR]; omega)), ew i h6 h7 (by omega)]
  · rw [mt', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [mt', word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide), ite_eq_left rfl]
  · rw [zt, z4]
    show some (w3.gpr .ebx - 1 == 0) = _
    rw [c3]
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> rfl

/-- `Input` of the first 57 bytes. -/
theorem Input.take57 {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N) (hN : 57 ≤ N) :
    Input s base p 57 :=
  ⟨by have := h.fit; omega, fun i hi => h.read i (by omega), fun i hi => h.far i (by omega)⟩

/-- An iteration's second part, after `vbodyA_ok`: from `m` decodings left to `m - 1`. -/
theorem vbodyB_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) {sig pk : BitVec 32}
    (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57) (ipk : Input s base pk 57)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) {m : Nat} (hm : 1 ≤ m)
    {t u : State} (ht : DecInv base s sig pk m t) (hA : AFacts base t u) :
    WP isa (.seq (decode 6 7) (.block vnext)) u fun v =>
      DecInv base s sig pk (m - 1) v ∧ v.zf = some (decide (m - 1 = 0)) := by
  obtain ⟨ae, ak, ao, arx, ary⟩ := hA
  have hst := ht.scr hs
  have kt := ht.keeps.trans ak
  have hsu := hs.of_keeps kt (by decide)
  have Ou : Outside base 0 8192 s.mem u.mem :=
    (ht.frame.whole (by decide) (by decide)).trans (ao.mono (by decide) (by decide))
  have DAu : DFrame base t.mem u.mem := DFrame.of_out ao (by decide) (by decide)
  have Eu : ∀ i : Index, E u.mem base i = E t.mem base i := fun i =>
    E_out ao i (Or.inl (by have := slot_range i; simp only [RX]; omega))
  have bu : BoundedEnv u.mem base := BoundedEnv.out ao (by decide) ht.bounded
  have badu : word u.mem base BAD = word t.mem base BAD := ao.word (Or.inl (by decide)) (by decide)
  have h10u : E u.mem base 10 = 1 := by rw [Eu, ht.other 10 (by decide) (by decide) (by decide), h10]
  have h11u : E u.mem base 11 = Spec.Ed448.d := by rw [Eu, ht.other 11 (by decide) (by decide) (by decide), h11]
  have hc : word u.mem base CNT = BitVec.ofNat 32 (m - 1 + 1) := by
    rw [ao.word (Or.inr (by decide)) (by decide), ht.cnt, Nat.sub_add_cancel hm]
  have hp : u.gpr .esi = (if m = 2 then sig else pk) := ae.trans (ht.ptr hm)
  have hin : Input u base (if m = 2 then sig else pk) 57 := by
    split
    · exact isig.of_keeps kt
    · exact ipk.of_keeps kt
  have dec : decAt u.mem (if m = 2 then sig else pk) = decAt s.mem (if m = 2 then sig else pk) := by
    split
    · exact congrArg Spec.Ed448.decodePoint (isig.bytes Ou)
    · exact congrArg Spec.Ed448.decodePoint (ipk.bytes Ou)
  refine WP.mono (vdecodeRest_ok hR hsu bu hp hin h10u h11u (hpk.of kt (by decide) Ou) (c := m - 1)
    (by have := ht.le; omega) hc) fun v ⟨kv, Dv, bv, cv, vv, ev, xv, yv, pv, nv, zv⟩ => ?_
  rw [dec] at cv vv
  refine ⟨⟨by have := ht.le; omega, kt.trans kv, (ht.frame.trans DAu).trans Dv, bv, nv, fun h => ?_,
    fun i h6 h7 hi => by rw [ev i h6 h7 hi, Eu, ht.other i h6 h7 hi], ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun h => ?_⟩, zv⟩
  · have : m = 2 := by have := ht.le; omega
    subst this
    rw [pv]; rfl
  · rw [badu] at cv
    refine (ht.bad.trans cv).congr ?_
    rcases (by have := ht.le; omega : m = 1 ∨ m = 2) with rfl | rfl
    · exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨fun _ => h1 (by decide), fun _ => h2⟩,
        fun ⟨h1, h2⟩ => ⟨⟨fun _ => h1 (by decide), fun h => absurd h (by decide)⟩, h2 rfl⟩⟩
    · exact ⟨fun ⟨_, h2⟩ => ⟨fun _ => h2, fun h => absurd h (by decide)⟩,
        fun ⟨h1, _⟩ => ⟨⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩, h1 (by decide)⟩⟩
  · have : m = 2 := by omega
    subst this
    exact vv
  · have : m = 1 := by omega
    subst this
    intro r hr
    obtain ⟨x, y, z⟩ := ht.rIn rfl r hr
    refine ⟨?_, ?_, z⟩
    · show Proof.X448.toFe (fe v.mem base RX) = r.X
      rw [← x]
      exact congrArg Proof.X448.toFe (valN_congr fun i hi => (xv i hi).trans (arx i hi))
    · show Proof.X448.toFe (fe v.mem base RY) = r.Y
      rw [← y]
      exact congrArg Proof.X448.toFe (valN_congr fun i hi => (yv i hi).trans (ary i hi))
  · have : m = 1 := by omega
    subst this
    exact ⟨fun i hi => by rw [xv i hi, arx i hi]; exact ht.bounded 6 i hi,
      fun i hi => by rw [yv i hi, ary i hi]; exact ht.bounded 7 i hi⟩
  · have : m = 1 := by omega
    subst this
    exact vv

/-- One iteration, from `m` decodings left to `m - 1`. -/
theorem vdecodeStep_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) {sig pk : BitVec 32}
    (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57) (ipk : Input s base pk 57)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) {m : Nat} (hm : 1 ≤ m)
    {t : State} (ht : DecInv base s sig pk m t) :
    WP isa vdecodeBody t fun v => DecInv base s sig pk (m - 1) v ∧ v.zf = some (decide (m - 1 = 0)) := by
  rw [vdecodeBody]
  exact WP.seq (WP.mono (vbodyA_ok (ht.scr hs)) fun u hA =>
    vbodyB_ok hR hs hpk isig ipk h10 h11 hm ht hA)

/-- `R` (at `sig`) decoded and kept at `RX` and `RY`, then `A` (at `pk`) into slots 6–7. -/
theorem vdecode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sig pk : BitVec 32} (hsig : ArgAt s base 8 sig) (hpk : ArgAt s base 4 pk) (isig : Input s base sig 57)
    (ipk : Input s base pk 57) (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa vdecode s (DecInv base s sig pk 0) := by
  rw [vdecode]
  refine WP.seq (WP.mono (vdecodeInit_ok hs hb (pk := pk) hsig) fun t ht => ?_)
  refine WP.loop (M := isa) (fun n (t : State) => 1 ≤ n ∧ DecInv base s sig pk n t) ?_ 2 t ⟨by decide, ht⟩
  intro n u ⟨hn, hu⟩
  refine WP.mono (vdecodeStep_ok hR hs hpk isig ipk h10 h11 hn hu) fun v ⟨hv, zv⟩ => ?_
  rcases (by have := hu.le; omega : n = 1 ∨ n = 2) with rfl | rfl
  · exact .inl ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, hv⟩
  · exact .inr ⟨by show v.zf.map (!·) = _; rw [zv]; rfl, 1, by decide, by decide, hv⟩

/-- `R` copied into slots 8 and 9. -/
theorem vR_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hx : Bounded s.mem base RX) (hy : Bounded s.mem base RY) :
    WP isa (.block vR) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base 8 = F s.mem base RX ∧
      E t.mem base 9 = F s.mem base RY ∧ (∀ i : Index, i ≠ 8 → i ≠ 9 → E t.mem base i = E s.mem base i) := by
  rw [vR, WP.block_append_iff]
  refine WP.mono (copy_ok hs (o := slot 8) (a := RX) (by decide) (by decide) (Or.inr (Or.inl (by decide))))
    fun s1 ⟨f1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (copy_ok hs1 (o := slot 9) (a := RY) (by decide) (by decide) (Or.inr (Or.inl (by decide))))
    fun t ⟨f2, o2, k2⟩ => ?_
  have O : Outside base 64 2816 s.mem t.mem := (o1.mono (by decide) (by decide)).trans (o2.mono (by decide) (by decide))
  have l8 : ∀ j < 28, limbs t.mem base (slot 8) j = limbs s.mem base RX j := fun j hj => by
    rw [o2.limbs (Or.inl (by decide)) (by decide) hj, f1 j hj]
  have l9 : ∀ j < 28, limbs t.mem base (slot 9) j = limbs s.mem base RY j := fun j hj => by
    rw [f2 j hj, o1.limbs (Or.inr (by decide)) (by decide) hj]
  have lo : ∀ i : Index, i ≠ 8 → i ≠ 9 → ∀ j < 28, limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j :=
    fun i h8 h9 j hj => by
      have := slot_range i
      rw [o2.limbs (slot_sep (j := 9) h9) (by omega) hj, o1.limbs (slot_sep (j := 8) h8) (by omega) hj]
  refine ⟨⟨(k1.mono ?_).trans (k2.mono ?_), fun p hp _ => O p hp⟩, fun i j hj => ?_, ?_, ?_,
    fun i h8 h9 => ?_⟩
  · intro r hr; revert r; decide
  · intro r hr; revert r; decide
  · by_cases h8 : i = 8
    · subst h8; exact (l8 j hj) ▸ hx j hj
    · by_cases h9 : i = 9
      · subst h9; exact (l9 j hj) ▸ hy j hj
      · rw [lo i h8 h9 j hj]; exact hb i j hj
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr l8)
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr l9)
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (valN_congr (lo i h8 h9))

/-- A field element at `RX` or `RY`, through the field arithmetic (which writes below them). -/
theorem F_high {base : Addr} {x nx : Nat} {m m' : Mem} (h : Outside2 base x nx ACC 512 m m') (hx : x + nx ≤ 4096)
    {o : Nat} (ho : o = RX ∨ o = RY) : F m' base o = F m base o ∧ (Bounded m base o → Bounded m' base o) := by
  have l : ∀ j < 28, limbs m' base o j = limbs m base o j := fun j hj =>
    congrArg BitVec.toNat (h.word (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega))
      (Or.inr (by rcases ho with rfl | rfl <;> simp only [RX, RY, ACC] <;> omega))
      (by rcases ho with rfl | rfl <;> simp only [RX, RY] <;> omega))
  exact ⟨congrArg Proof.X448.toFe (valN_congr l), fun hb j hj => by rw [l j hj]; exact hb j hj⟩

end VG.Proof.Ed448.X86
