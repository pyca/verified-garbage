import VerifiedGarbage.Proof.Ed25519.X86.VerifyDecodeInput
import VerifiedGarbage.Proof.Ed25519.X86.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.X86.VerifyTables
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.Group.Decode

/-!
# Ed25519 verification on x86: `A` and `R` decoded by one loop

`decodeBoth` decodes `A` (`pk`), then `R` (the signature's first half), with one copy of the
decoding: the encoding's pointer, `R`'s, the table entry's offset and the AND of the results
are words of the working space (`DPTR`, `DNEXT`, `DTAB`, `DOK`, `DecAt`). Each iteration
(`decodeBody_ok`) decodes the encoding at `[DPTR]`, ANDs its result into `DOK` and writes the
point to the table at `[DTAB]` (`A` at 7680, `R` at 7808); `verifyDecode` then runs the
equation if both are points (`verifyDecode_ok`).
-/

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def equationResult (s : State) (a r : Spec.Ed25519.Point) : Bool :=
  Spec.Ed25519.pointEqual (Spec.Ed25519.pointMul (verificationScalar s) Spec.Ed25519.basePoint)
    (Spec.Ed25519.pointAdd r (Spec.Ed25519.pointMul (verificationChallenge s) a))

def decodeRResult (s : State) (a : Spec.Ed25519.Point) : Bool :=
  match inputPoint s 1 with | none => false | some r => equationResult s a r

def decodeResult (s : State) : Bool :=
  match inputPoint s 0 with | none => false | some a => decodeRResult s a

/-- The AND of the first `k` decodings' successes. -/
def decOk (s : State) : Nat → Bool
  | 0 => true
  | k + 1 => decOk s k && (inputPoint s k).isSome

/-- Before the decoding `k` (`A`'s, then `R`'s): the loop's words, and the points decoded so
far in the table. -/
structure DecAt (s₀ : State) (k : Nat) (s : State) : Prop where
  saved : Saved s₀ (arg s₀ 3) s
  ptr : k < 2 → wd s.mem (arg s₀ 3) DPTR = arg s₀ k
  next : wd s.mem (arg s₀ 3) DNEXT = arg s₀ 1
  tab : wd s.mem (arg s₀ 3) DTAB = BitVec.ofNat 32 (7680 + 128 * k)
  ok : wd s.mem (arg s₀ 3) DOK = signWord (decOk s₀ k)
  pts : ∀ j < k, ∀ p, inputPoint s₀ j = some p → tablePoint s.mem (arg s₀ 3) (7680 + 128 * j) = p

theorem decodeFlag {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .eax = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

theorem decodePt {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : ∀ q, p = some q → point (env s.mem base) 0 1 2 3 = q := by
  intro q hq
  subst hq
  exact h.2

theorem decodeFlag_eq {base : BitVec 32} {p p' : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) (he : p = p') : s.gpr .eax = signWord p'.isSome := he ▸ decodeFlag h

theorem decodePt_eq {base : BitVec 32} {p p' : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) (he : p = p') :
    ∀ q, p' = some q → point (env s.mem base) 0 1 2 3 = q := he ▸ decodePt h

theorem decOk_succ (s : State) (k : Nat) : decOk s (k + 1) = (decOk s k && (inputPoint s k).isSome) := rfl

theorem signWord_and (a b : Bool) : signWord a &&& signWord b = signWord (a && b) := by
  cases a <;> cases b <;> rfl

/-- A store of `r` to a word of the loop's (from `DPTR`), keeping what the code saved. -/
theorem storeLoop_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) {d : Nat}
    (hd : DPTR ≤ d) (hd' : d + 4 ≤ DPTR + 16) (r : Reg) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Saved s₀ (arg s₀ 3) t → t.mem = s.mem.writeW (addr (arg s₀ 3) d) (s.gpr r) →
      t.gpr = s.gpr → t.zf = s.zf → WP isa (.block is) t Q) :
    WP isa (.block (.store (Impl.X25519.X86.sc d) r :: is)) s Q := by
  have cs := hs.ctx hp.scratch.fit hp.scratch.wr
  simp only [DPTR] at hd hd'
  refine Wp.wp_stm hs.edi (cs.inW (d := d) (n := 4) (by omega) (by decide)) fun t ht => k t ?_ ht.mem ht.gpr ht.zf
  refine hs.of_offset hp.scratch.fit ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩ (o := DPTR) (n := 16)
    ?_ (by decide) (by decide) (by decide)
  rw [ht.mem]
  exact frame_write1 (Frame.refl _ _) hp.scratch.fit (by decide) (by simp only [DPTR]; omega)
    (by simp only [DPTR]; omega) _

/-- A load of a word of the working space. -/
theorem loadWd_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) {d : Nat}
    (hd : d + 4 ≤ 8192) (r : Reg) (hr : r ≠ .edi ∧ r ≠ .esp) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Saved s₀ (arg s₀ 3) t → t.gpr r = wd s.mem (arg s₀ 3) d →
      (∀ r', r' ≠ r → t.gpr r' = s.gpr r') → t.mem = s.mem → WP isa (.block is) t Q) :
    WP isa (.block (.mov r (.mem (Impl.X25519.X86.sc d)) :: is)) s Q := by
  have cs := hs.ctx hp.scratch.fit hp.scratch.wr
  refine Wp.wp_ldm hs.edi (cs.inRW (d := d) (n := 4) hd (by decide)) fun t ht => k t ?_ ht.gpr ht.other ht.mem
  exact ⟨(ht.other _ hr.1.symm).trans hs.edi, (ht.other _ hr.2.symm).trans hs.esp, ht.rd.trans hs.rd,
    ht.wr.trans hs.wr, by rw [ht.mem]; exact hs.frame, by rw [ht.mem]; exact hs.saved⟩

theorem Saved.upd {s₀ s t : State} {x : BitVec 32} (h : Saved s₀ x s) {r : Reg} {v : BitVec 32}
    (hu : Wp.Upd s t r v) (hr : r ≠ .edi ∧ r ≠ .esp := by decide) : Saved s₀ x t :=
  ⟨(hu.other _ hr.1.symm).trans h.edi, (hu.other _ hr.2.symm).trans h.esp, hu.rd.trans h.rd,
    hu.wr.trans h.wr, by rw [hu.mem]; exact h.frame, by rw [hu.mem]; exact h.saved⟩

/-- A word of the working space after a store to another word (or the same one). -/
theorem wd_store {x : BitVec 32} (hx : x.toNat + 8192 ≤ 2 ^ 32) (m : Mem) (w : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 8192) (he : e + 4 ≤ 8192) (h : d = e ∨ d + 4 ≤ e ∨ e + 4 ≤ d) :
    wd (m.writeW (addr x e) w) x d = if d = e then w else wd m x d := by
  rcases h with rfl | h
  · rw [ite_eq_left rfl]; exact wd_write_self m x w d
  · rw [ite_eq_right (by omega)]
    exact wd_write_ne m w (by omega) (by omega) h

theorem decodeStart_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa (.block decodeStart) s (DecAt s₀ 0) := by
  have hx := hp.scratch.fit
  rw [decodeStart]
  refine Wp.wp_ldm hs.esp (by rw [hs.rd, hs.wr]; exact hp.scratch.argIn (i := 0) (by decide)) fun s1 h1 => ?_
  have hs1 := hs.upd h1
  refine storeLoop_ok hp hs1 (d := DPTR) (Nat.le_refl _) (by decide) .eax fun s2 hs2 m2 g2 _ => ?_
  refine Wp.wp_ldm hs2.esp (by rw [hs2.rd, hs2.wr]; exact hp.scratch.argIn (i := 1) (by decide))
    fun s3 h3 => ?_
  have hs3 := hs2.upd h3
  refine storeLoop_ok hp hs3 (d := DNEXT) (by decide) (by decide) .eax fun s4 hs4 m4 g4 _ => ?_
  refine Wp.wp_movi fun s5 h5 => ?_
  have hs5 := hs4.upd h5
  refine storeLoop_ok hp hs5 (d := DTAB) (by decide) (by decide) .eax fun s6 hs6 m6 g6 _ => ?_
  refine Wp.wp_movi fun s7 h7 => ?_
  have hs7 := hs6.upd h7
  refine storeLoop_ok hp hs7 (d := DOK) (by decide) (by decide) .eax fun t ht mt gt _ => WP.block_nil ?_
  have a0 : s1.gpr .eax = arg s₀ 0 := by
    rw [h1.gpr]; exact hp.scratch.arg_same hs.frame (i := 0) (by decide)
  have a1 : s3.gpr .eax = arg s₀ 1 := by
    rw [h3.gpr]; exact hp.scratch.arg_same hs2.frame (i := 1) (by decide)
  have em : t.mem = (((s.mem.writeW (addr (arg s₀ 3) DPTR) (arg s₀ 0)).writeW (addr (arg s₀ 3) DNEXT) (arg s₀ 1)).writeW
      (addr (arg s₀ 3) DTAB) (7680 : BitVec 32)).writeW (addr (arg s₀ 3) DOK) (1 : BitVec 32) := by
    rw [mt, h7.gpr, h7.mem, m6, h5.gpr, h5.mem, m4, a1, h3.mem, m2, a0, h1.mem]
  refine ⟨ht, fun _ => ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [em, wd_store hx _ _ (by decide) (by decide) (by decide), wd_store hx _ _ (by decide) (by decide) (by decide),
      wd_store hx _ _ (by decide) (by decide) (by decide), wd_store hx _ _ (by decide) (by decide) (by decide)]
    rfl
  · rw [em, wd_store hx _ _ (by decide) (by decide) (by decide), wd_store hx _ _ (by decide) (by decide) (by decide),
      wd_store hx _ _ (by decide) (by decide) (by decide)]
    rfl
  · rw [em, wd_store hx _ _ (by decide) (by decide) (by decide), wd_store hx _ _ (by decide) (by decide) (by decide)]
    rfl
  · rw [em, wd_store hx _ _ (by decide) (by decide) (by decide)]
    rfl

/-- The encoding at `[DPTR]` (the input `k`) copied to slot 3. -/
theorem decodeLoad_ok {s₀ s : State} {k : Nat} (hp : VerifyPre s₀)
    (hi : SlicePre s₀ 3 (arg s₀ k + BitVec.ofNat 32 0) 32) (hs : Saved s₀ (arg s₀ 3) s)
    (hptr : wd s.mem (arg s₀ 3) DPTR = arg s₀ k) :
    WP isa (.block decodeLoad) s fun t => Saved s₀ (arg s₀ 3) t ∧
      (∀ j < 8, wd t.mem (arg s₀ 3) (96 + 4 * j) = wd s₀.mem (arg s₀ k + BitVec.ofNat 32 0) (4 * j)) ∧
      Frame [sub (arg s₀ 3) 96 (4 * 8)] s.mem t.mem := by
  rw [decodeLoad]
  refine loadWd_ok hp hs (d := DPTR) (by decide) .esi (by decide) fun u hu eu _ mu => ?_
  have cu := hu.ctx hp.scratch.fit hp.scratch.wr
  have eu' : u.gpr .esi = arg s₀ k + BitVec.ofNat 32 0 := by rw [eu, hptr]; exact (BitVec.add_zero _).symm
  have hr : ∀ j < 8, InRegions (u.rd ++ u.wr) (addr (arg s₀ k + BitVec.ofNat 32 0) (4 * j)) 4 := by
    intro j hj; rw [hu.rd, hu.wr]
    exact slice_read hi (by omega_using [hj]) (by decide)
  have hsep : ∀ j < 8, (sub (arg s₀ k + BitVec.ofNat 32 0) (4 * j) 4).Disjoint (sub (arg s₀ 3) 96 (4 * 8)) := by
    intro j hj
    refine (hi.sep.sub_left (slice_sub hi (by omega_using [hj]) (by decide))).sub_right ?_
    rw [scR_eq]; exact sub_sub hp.scratch.fit (Nat.zero_le _) (by decide) (by decide)
  refine WP.mono (copyWords_ok cu eu' (by decide) hr hsep 8 (Nat.le_refl _)) fun t ht => ?_
  refine ⟨hu.of_offset hp.scratch.fit (Keep.scalar ht.keep) ht.frame (by decide) (by decide) (by decide), ?_,
    by rw [← mu]; exact ht.frame⟩
  intro j hj
  rw [ht.words j hj]
  exact hu.frame.readW (slice_contains hi (by omega_using [hj]) (by decide))
    (by simp only [List.mem_singleton]; rintro r rfl; exact hi.sep) (by decide)

/-- The input `k` decoded: its result in `eax`, and its point in slots 0–3. -/
theorem decodeOne_ok {s₀ s : State} {k : Nat} (hp : VerifyPre s₀)
    (hi : SlicePre s₀ 3 (arg s₀ k + BitVec.ofNat 32 0) 32) (hs : Saved s₀ (arg s₀ 3) s)
    (hptr : wd s.mem (arg s₀ 3) DPTR = arg s₀ k) :
    WP isa (.seq (.block decodeLoad) pointDecode) s fun t =>
      Saved s₀ (arg s₀ 3) t ∧ Frame [sub (arg s₀ 3) 24 7144] s.mem t.mem ∧
      t.gpr .eax = signWord (inputPoint s₀ k).isSome ∧
      (∀ q, inputPoint s₀ k = some q → point (env t.mem (arg s₀ 3)) 0 1 2 3 = q) := by
  refine WP.seq (WP.mono (decodeLoad_ok hp hi hs hptr) fun a ⟨ha, wa, fa⟩ => ?_)
  refine WP.mono (pointDecode_ok (ha.ctx hp.scratch.fit hp.scratch.wr)) fun t ht => ?_
  have kt := ht.1
  refine ⟨ha.mulkeep hp.scratch.fit kt,
    (frameWiden fa hp.scratch.fit (by decide) (by decide) (by decide)).trans kt.frame, ?_⟩
  have value : fe a.mem (arg s₀ 3) 96 = fe s₀.mem (arg s₀ k + BitVec.ofNat 32 0) 0 := by
    apply num_congr
    intro j hj
    simp only [Nat.zero_add]
    exact congrArg BitVec.toNat (wa j hj)
  have h2 := Eq.mp (congrArg (fun n => DecodeResult (arg s₀ 3) (decodeNumber n) t) value) ht.2
  exact ⟨decodeFlag_eq h2 (inputPoint_number hi), decodePt_eq h2 (inputPoint_number hi)⟩

theorem decodeNext_eq : decodeNext = ([.mov .ecx (.reg .eax), .mov .edx (.mem (Impl.X25519.X86.sc DTAB)),
    .alu .add .edx (.reg .edi)] : List Instr) ++ (pointToTable ++
    ([.mov .edx (.mem (Impl.X25519.X86.sc DOK)), .alu .and .edx (.reg .ecx), .store (Impl.X25519.X86.sc DOK) .edx,
      .mov .eax (.mem (Impl.X25519.X86.sc DNEXT)), .store (Impl.X25519.X86.sc DPTR) .eax,
      .mov .edx (.mem (Impl.X25519.X86.sc DTAB)), .alu .add .edx (.imm 128), .store (Impl.X25519.X86.sc DTAB) .edx,
      .alu .cmp .edx (.imm 7936)] : List Instr)) := by
  simp only [decodeNext, List.append_assoc]

/-- The table entry at `[DTAB]` (`o = 7680 + 128 k`), and the loop's words. -/
theorem decodeNext_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) {k : Nat}
    (hk : k < 2) {p : Option Spec.Ed25519.Point} (hflag : s.gpr .eax = signWord p.isSome)
    (hpt : ∀ q, p = some q → point (env s.mem (arg s₀ 3)) 0 1 2 3 = q)
    (htab : wd s.mem (arg s₀ 3) DTAB = BitVec.ofNat 32 (7680 + 128 * k)) :
    WP isa (.block decodeNext) s fun t => Saved s₀ (arg s₀ 3) t ∧
      wd t.mem (arg s₀ 3) DOK = (wd s.mem (arg s₀ 3) DOK &&& signWord p.isSome) ∧
      wd t.mem (arg s₀ 3) DPTR = wd s.mem (arg s₀ 3) DNEXT ∧
      wd t.mem (arg s₀ 3) DNEXT = wd s.mem (arg s₀ 3) DNEXT ∧
      wd t.mem (arg s₀ 3) DTAB = BitVec.ofNat 32 (7680 + 128 * (k + 1)) ∧
      (∀ q, p = some q → tablePoint t.mem (arg s₀ 3) (7680 + 128 * k) = q) ∧
      (∀ o, o + 128 ≤ 7680 + 128 * k → tablePoint t.mem (arg s₀ 3) o = tablePoint s.mem (arg s₀ 3) o) ∧
      t.zf = some (decide (k = 1)) := by
  have hx := hp.scratch.fit
  have eax0 : s.gpr .eax = signWord p.isSome := hflag
  rw [decodeNext_eq, WP.block_append_iff]
  refine Wp.wp_mov fun u1 h1 => ?_
  have hs1 := hs.upd h1
  refine loadWd_ok hp hs1 (d := DTAB) (by decide) .edx (by decide) fun u2 hs2 e2 g2 m2 => ?_
  refine Wp.wp_add fun u3 h3 _ => WP.block_nil ?_
  have hs3 := hs2.upd h3
  have m3 : u3.mem = s.mem := by rw [h3.mem, m2, h1.mem]
  have ed3 : u3.gpr .edx = arg s₀ 3 + BitVec.ofNat 32 (7680 + 128 * k) := by
    rw [h3.gpr, e2, h1.mem, htab, g2 _ (by decide), h1.other _ (by decide), hs.edi, BitVec.add_comm]
  have ec3 : u3.gpr .ecx = signWord p.isSome := by
    rw [h3.other _ (by decide), g2 _ (by decide), h1.gpr, eax0]
  rw [WP.block_append_iff]
  refine WP.mono (pointToTable_ok (hs3.ctx hx hp.scratch.wr) ed3 (by omega) (by omega)) fun u4 ⟨k4, t4⟩ => ?_
  have hs4 : Saved s₀ (arg s₀ 3) u4 :=
    hs3.of_offset hx ⟨k4.gpr _ (by decide), k4.gpr _ (by decide), k4.rd, k4.wr⟩ k4.frame (by omega) (by omega)
      (by omega)
  have w4 : ∀ d, 7936 ≤ d → d + 4 ≤ 8192 → wd u4.mem (arg s₀ 3) d = wd s.mem (arg s₀ 3) d := fun d h1 h2 => by
    rw [wd_frame1 k4.frame hx (by omega) h2 (Or.inr (by omega)), m3]
  have ec4 : u4.gpr .ecx = signWord p.isSome := (k4.gpr _ (by decide)).trans ec3
  refine loadWd_ok hp hs4 (d := DOK) (by decide) .edx (by decide) fun u5 hs5 e5 g5 m5 => ?_
  refine Wp.wp_and fun u6 h6 => ?_
  have hs6 := hs5.upd h6
  refine storeLoop_ok hp hs6 (d := DOK) (by decide) (by decide) .edx fun u7 hs7 m7 g7 _ => ?_
  refine loadWd_ok hp hs7 (d := DNEXT) (by decide) .eax (by decide) fun u8 hs8 e8 g8 m8 => ?_
  refine storeLoop_ok hp hs8 (d := DPTR) (Nat.le_refl _) (by decide) .eax fun u9 hs9 m9 g9 _ => ?_
  refine loadWd_ok hp hs9 (d := DTAB) (by decide) .edx (by decide) fun u10 hs10 e10 g10 m10 => ?_
  refine Wp.wp_addi fun u11 h11 => ?_
  have hs11 := hs10.upd h11
  refine storeLoop_ok hp hs11 (d := DTAB) (by decide) (by decide) .edx fun u12 hs12 m12 g12 _ => ?_
  refine Wp.wp_cmpi fun t ht _ zt => WP.block_nil ?_
  -- The memory: the table entry, then three stores.
  have dok : u7.gpr .edx = wd s.mem (arg s₀ 3) DOK &&& signWord p.isSome := by
    rw [g7, h6.gpr, e5, w4 DOK (by decide) (by decide), g5 _ (by decide), ec4]
  have dnx : u9.gpr .eax = wd s.mem (arg s₀ 3) DNEXT := by
    rw [g9, e8, m7, wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide), h6.mem, m5,
      w4 DNEXT (by decide) (by decide)]
  have mt : t.mem = ((u4.mem.writeW (addr (arg s₀ 3) DOK) (u7.gpr .edx)).writeW (addr (arg s₀ 3) DPTR)
      (u9.gpr .eax)).writeW (addr (arg s₀ 3) DTAB) (u12.gpr .edx) := by
    rw [ht.mem, m12, h11.mem, m10, m9, m8, m7, h6.mem, m5, g7, g9, g12]
  have tab12 : u12.gpr .edx = BitVec.ofNat 32 (7680 + 128 * (k + 1)) := by
    rw [g12, h11.gpr, e10, m9, wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide), m8,
      m7, wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide), h6.mem, m5,
      w4 DTAB (by decide) (by decide), htab]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide
  have frm : Frame [sub (arg s₀ 3) DPTR 16] u4.mem t.mem := by
    rw [mt]
    exact frame_write1 (frame_write1 (frame_write1 (Frame.refl _ _) hx (by decide) (by decide) (by decide) _) hx
      (by decide) (by decide) (by decide) _) hx (by decide) (by decide) (by decide) _
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_, fun o ho => ?_, ?_⟩
  · exact hs12.of_offset hx ⟨by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩ (o := DPTR) (n := 16)
      (by rw [ht.mem]; exact Frame.refl _ _) (by decide) (by decide) (by decide)
  · rw [mt, wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_left rfl, dok]
  · rw [mt, wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_left rfl, dnx]
  · rw [mt, wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide),
      wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_right (by decide), w4 DNEXT (by decide) (by decide)]
  · rw [mt, wd_store hx _ _ (by decide) (by decide) (by decide), ite_eq_left rfl, tab12]
  · rw [tablePoint_frame hx frm (by decide) (by omega) (Or.inl (by simp only [DPTR]; omega)), t4, m3]
    exact hpt q hq
  · rw [tablePoint_frame hx frm (by decide) (by omega) (Or.inl (by simp only [DPTR]; omega)),
      tablePoint_frame hx k4.frame (by omega) (by omega) (Or.inl ho), m3]
  · rw [zt, tab12]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> decide

/-- One iteration: the input `k` decoded, its result ANDed into `DOK`, and its point in the
table. -/
theorem decodeBody_ok {s₀ s : State} (hp : VerifyPre s₀) {k : Nat} (hk : k < 2) (hs : DecAt s₀ k s) :
    WP isa decodeBody s fun t => DecAt s₀ (k + 1) t ∧ t.zf = some (decide (k = 1)) := by
  have hx := hp.scratch.fit
  have hi : SlicePre s₀ 3 (arg s₀ k + BitVec.ofNat 32 0) 32 := by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    exacts [hp.pk, hp.r]
  rw [decodeBody]
  apply WP.assoc
  refine WP.seq (WP.mono (decodeOne_ok hp hi hs.saved (hs.ptr hk)) fun a hd => ?_)
  have ha := hd.1
  have fa := hd.2.1
  have wa : ∀ d, 7168 ≤ d → d + 4 ≤ 8192 → wd a.mem (arg s₀ 3) d = wd s.mem (arg s₀ 3) d :=
    fun d h1 h2 => wd_frame1 fa hx (by decide) h2 (Or.inr (by omega))
  refine WP.mono (decodeNext_ok hp ha hk hd.2.2.1 hd.2.2.2 (by rw [wa DTAB (by decide) (by decide)]; exact hs.tab))
    fun t hn => ?_
  have ok := hn.2.1
  have ptr := hn.2.2.1
  have nx := hn.2.2.2.1
  have old := hn.2.2.2.2.2.2.1
  refine ⟨⟨hn.1, fun hk1 => ?_, ?_, hn.2.2.2.2.1, ?_, fun j hj q hq => ?_⟩, hn.2.2.2.2.2.2.2⟩
  · obtain rfl : k = 0 := by omega
    rw [ptr, wa DNEXT (by decide) (by decide)]; exact hs.next
  · rw [nx, wa DNEXT (by decide) (by decide)]; exact hs.next
  · rw [ok, wa DOK (by decide) (by decide), hs.ok, signWord_and, decOk_succ]
  · rcases (by omega : j = k ∨ j < k) with rfl | hj'
    · exact hn.2.2.2.2.2.1 q hq
    · rw [old _ (by omega), tablePoint_frame hx fa (by decide) (by omega) (Or.inr (by omega))]
      exact hs.pts j hj' q hq

/-- `A` and `R` decoded, by the loop. -/
theorem decodeBoth_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa decodeBoth s (DecAt s₀ 2) := by
  rw [decodeBoth]
  refine WP.seq (WP.mono (decodeStart_ok hp hs) fun a ha => ?_)
  refine WP.loop (M := isa) (Inv := fun m t => ∃ k, k + m = 2 ∧ k < 2 ∧ DecAt s₀ k t) ?_ 2 a
    ⟨0, rfl, by decide, ha⟩
  intro m u ⟨k, hkm, hk, hu⟩
  refine WP.mono (decodeBody_ok hp hk hu) fun t ⟨ht, zt⟩ => ?_
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact .inr ⟨by show t.zf.map (!·) = _; rw [zt]; rfl, 1, by omega, 1, rfl, by decide, ht⟩
  · exact .inl ⟨by show t.zf.map (!·) = _; rw [zt]; rfl, ht⟩

theorem decOk_two (s : State) :
    decOk s 2 = ((inputPoint s 0).isSome && (inputPoint s 1).isSome) := by
  simp only [decOk, Bool.true_and]

/-- Both decoded, and the equation if both are points. -/
theorem verifyDecode_ok {s₀ s : State} (hp : VerifyPre s₀) (hs : Saved s₀ (arg s₀ 3) s) :
    WP isa verifyDecode s fun t => Saved s₀ (arg s₀ 3) t ∧ t.gpr .eax = signWord (decodeResult s₀) := by
  rw [verifyDecode]
  refine WP.seq (WP.mono (decodeBoth_ok hp hs) fun a ha => ?_)
  refine WP.seq (loadWd_ok hp ha.saved (d := DOK) (by decide) .eax (by decide) fun b hb eb _ mb =>
    Wp.wp_test fun c hc zc => WP.block_nil ?_)
  have hsc : Saved s₀ (arg s₀ 3) c := ⟨by rw [hc.gpr]; exact hb.edi, by rw [hc.gpr]; exact hb.esp,
    hc.rd.trans hb.rd, hc.wr.trans hb.wr, by rw [hc.mem]; exact hb.frame, by rw [hc.mem]; exact hb.saved⟩
  have mc : c.mem = a.mem := hc.mem.trans mb
  apply WP.ite (decOk s₀ 2) (by
    show c.zf.map (!·) = _
    rw [zc, eb, ha.ok, BitVec.and_self]
    cases decOk s₀ 2 <;> rfl)
  · intro hok
    rw [decOk_two, Bool.and_eq_true] at hok
    obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp hok.1
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp hok.2
    have tA : tablePoint c.mem (arg s₀ 3) 7680 = a0 := by rw [mc]; exact ha.pts 0 (by decide) a0 ha0
    have tR : tablePoint c.mem (arg s₀ 3) 7808 = r0 := by rw [mc]; exact ha.pts 1 (by decide) r0 hr0
    obtain ⟨Aa, hAa⟩ := VG.Proof.Ed25519.decodePoint_rep ha0
    obtain ⟨Ra, hRa⟩ := VG.Proof.Ed25519.decodePoint_rep hr0
    refine WP.mono (verifyEquationPoints_ok hp hsc (by rw [tA]; exact hAa) (by rw [tR]; exact hRa))
      fun t ⟨ht, vt⟩ => ⟨ht, ?_⟩
    rw [vt, tA, tR]
    simp only [decodeResult, decodeRResult, ha0, hr0, equationResult]
  · intro hok
    refine WP.mono (recoverInvalid_ok c (arg s₀ 3)) fun t ⟨kt, rt⟩ => ?_
    refine ⟨hsc.ikeep hp.scratch.fit (IKeep.of_field kt), ?_⟩
    rw [decOk_two] at hok
    change t.gpr .eax = 0 at rt
    rw [rt]
    cases h0 : inputPoint s₀ 0 with
    | none => simp only [decodeResult, h0]; rfl
    | some a0 =>
      cases h1 : inputPoint s₀ 1 with
      | none => simp only [decodeResult, decodeRResult, h0, h1]; rfl
      | some r0 => rw [h0, h1] at hok; simp at hok

end VG.Proof.Ed25519.X86
