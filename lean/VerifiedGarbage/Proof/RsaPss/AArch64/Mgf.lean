import VerifiedGarbage.Proof.RsaPss.AArch64.MgfParts
import VerifiedGarbage.Proof.RsaPss.MgfBytes

/-!
# RSASSA-PSS on AArch64: MGF1

`mgfXor` XORs `MGF1(H, dbLen)` into `DB`, a counter at a time
(`round_ok`), where `H` is the `hLen` bytes after `DB` (`mgfXor_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strx eval_nonzero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss (getD_app i2osp_len mgf1_getD)

/-- `DB` with the first `n` bytes of the mask `mk` XORed in. -/
def mixV (V : Nat → Byte) (mk : List Byte) (e n : Nat) (o : Nat) : Byte :=
  if e ≤ o ∧ o < e + n then V o ^^^ mk.getD (o - e) 0 else V o

/-- What `mgfXor` may write: our working space, the stack below the frame,
and two slots. -/
abbrev mgfWr (F S : Addr) : List Region := [⟨S, oRsa⟩, below F 16, slotR F sNb, slotR F sDone]

theorem slot_keep {F : Addr} {d : Nat} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (slotR F d) r) :
    m'.readW (off F d) 64 = m.readW (off F d) 64 :=
  hf.readW (r := slotR F d) (Region.contains_self _ _) hd (by decide)

theorem Lay.doneD {t : State} {F S : Addr} (L : Lay t F S) :
    ∀ r ∈ [(⟨S, oRsa⟩ : Region), below F 16, slotR F sNb], Region.Disjoint (slotR F sDone) r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.dFS.sub_left (Offset.sub_base F (by decide))
  · exact slot_not_below F (by decide)
  · exact Offset.disjoint F (by decide) (by decide) (by decide)

theorem byte_of_bytesAt {m : Mem} {p : Addr} {n : Nat} {xs : List Byte} (h : Spec.Rsa.bytesAt m p n = xs)
    {k : Nat} (hk : k < n) : m (p + BitVec.ofNat 64 k) = xs.getD k 0 := by
  subst h
  simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- The loop's invariant after `c` counters. -/
structure MgfI (t : State) (F S : Addr) (V : Nat → Byte) (mk : List Byte) (e db D c : Nat) (v : State) :
    Prop where
  sp : v.sp = t.sp
  rd : v.rd = t.rd
  wr : v.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], v.gpr r = t.gpr r
  vec : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  x28 : v.gpr .x28 = BitVec.ofNat 64 c
  done : v.mem.readW (off F sDone) 64 = BitVec.ofNat 64 (c * D)
  fr : Frame (mgfWr F S) t.mem v.mem
  em : ∀ o, oEm ≤ o → o < oY → v.mem (off S o) = mixV V mk e (min (c * D) db) o

section
variable {H : Hash} (hH : HashOK H)

theorem round_ok {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {e db c : Nat}
    (hd : DbAt H.D e db) (h19 : t.gpr .x19 = off S oSt) (h21 : t.gpr .x21 = off S oDig)
    (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) {v : State}
    (I : MgfI t F S V (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db) e db H.D c v)
    (hc : c * H.D < db) :
    WP isa (seqs [clearBlock H, copyH H, .block (counter H), mgfHash H, xorOut H, .block (nextCtr H)]) v
      fun v' => (v'.gpr .x10 != 0) = decide ((c + 1) * H.D < db) ∧
        MgfI t F S V (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db) e db H.D (c + 1) v' := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hfit := hd.fit
  have he1 := hd.e1
  have c1 : oEm = 2560 := rfl
  have c2 : oY = 3584 := rfl
  have c3 : oDig = 2304 := rfl
  have c6 : oRsa = 8192 := rfl
  obtain ⟨hnb1, hnb, _⟩ := mgfNb_spec hH
  have hcD : c ≤ c * H.D := Nat.le_mul_of_pos_right _ hD
  have hs1 : (c + 1) * H.D = c * H.D + H.D := Nat.succ_mul _ _
  generalize hseed : (List.range H.D).map (fun i => V (e + db + i)) = seed at I ⊢
  generalize hmk : Spec.Mgf1.mgf1 G seed db = mk at I ⊢
  have Lv : Lay v F S := L.congr I.sp I.wr (I.cs .x20 (by decide))
  have Rv : Rep v.mem S (fun o => v.mem (off S o)) := fun _ _ => rfl
  unfold seqs seqs seqs seqs seqs
  -- `Y` cleared.
  refine WP.seq (WP.mono (clearBlock_ok hH Lv Rv) fun u1 ⟨k1, f1, R1⟩ => ?_)
  have L1 := Lv.congr k1.sp k1.wr (k1.get .x20)
  -- `H`.
  refine WP.seq (WP.mono (copyH_ok hH L1 R1 hd (by rw [k1.get .x24, I.cs .x24 (by decide), h24])
    (by rw [k1.get .x25, I.cs .x25 (by decide), h25])) fun u2 ⟨k2, f2, R2⟩ => ?_)
  have L2 := L1.congr k2.sp k2.wr (k2.get .x20)
  have hs : (List.range H.D).map (fun i => clr (fun o => v.mem (off S o)) oY (mgfNb H * H.P.B) (e + db + i)) =
      seed := by
    rw [← hseed]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [clr]
    rw [ite_eq_right (by omega_using [hfit, this]), I.em _ (by omega_using [he1]) (by omega_using [hfit, this])]
    simp only [mixV]
    rw [ite_eq_right (by omega_using [])]
  rw [hs] at R2
  -- The counter.
  refine WP.seq (WP.mono (counter_ok hH L2 R2 (c := c) (by rw [k2.get .x28, k1.get .x28, I.x28]) (by omega_using [hc, hfit, c2, hcD]))
    fun u3 ⟨k3, x22₃, nb₃, f3, R3⟩ => ?_)
  have L3 := L2.congr k3.sp k3.wr (k3.get .x20)
  have hsl : seed.length = H.D := by rw [← hseed, List.length_map, List.length_range]
  have hml : (seed ++ Spec.Rsa.i2osp c 4).length = H.D + 4 := by
    rw [List.length_append, hsl, i2osp_len]
  have g3 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u3.gpr r = t.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k3.get _ (by decide), k2.get _ (by decide), k1.get _ (by decide), I.cs _ (by decide)]
  -- The digest of `H ‖ C`.
  refine WP.seq (WP.mono (mgfHash_ok hH L3 R3 (msg := seed ++ Spec.Rsa.i2osp c 4) hml
    (by rw [g3 .x19 (by decide), h19]) (by rw [g3 .x21 (by decide), h21]) (by rw [x22₃, hml]) nb₃
    (by rw [hml]; omega_using [hnb1]) (by omega_using [hnb]) (fun i hi => ?_)) fun u4 ⟨O4, d4⟩ => ?_)
  · rw [getD_app, hsl]
    by_cases h1 : i < H.D
    · simp (disch := omega_arith) only [ctrV, updL, ite_eq_left, ite_eq_right]
      rw [Nat.add_sub_cancel_left]
    · by_cases h2 : i < H.D + 4
      · simp (disch := omega_arith) only [ctrV, ite_eq_left, ite_eq_right]
        rw [show oY + i - (oY + H.D) = i - H.D by omega_using []]
      · simp (disch := omega_arith) only [ctrV, updL, clr, ite_eq_left, ite_eq_right]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [i2osp_len]; omega_using [h2])]
        rfl
  have L4 := L3.congr O4.sp O4.wr (O4.cs .x20 (by decide))
  have g4 : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], u4.gpr r = t.gpr r := by
    intro r hr
    have := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [O4.cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), g3 r this]
  have done₄ : u4.mem.readW (off F sDone) 64 = BitVec.ofNat 64 (c * H.D) := by
    rw [slot_keep (O4.fr.mono (by simp)) L.doneD, slot_keep (f3.mono (by simp)) L.doneD,
      slot_keep (f2.mono (by simp)) L.doneD, slot_keep (f1.mono (by simp)) L.doneD, I.done]
  -- Into `DB`.
  refine WP.seq (WP.mono (xorOut_ok hH L4 (fun _ _ => rfl) hd (by rw [g4 .x24 (by decide), h24])
    (by rw [g4 .x25 (by decide), h25]) (by rw [g4 .x21 (by decide), h21]) done₄ hc) fun u5 ⟨k5, f5, R5⟩ => ?_)
  have L5 := L4.congr k5.sp k5.wr (k5.get .x20)
  have done₅ : u5.mem.readW (off F sDone) 64 = BitVec.ofNat 64 (c * H.D) := by
    rw [slot_keep (f5.mono (by simp)) L.doneD, done₄]
  -- The next counter.
  refine WP.mono (nextCtr_ok hH L5 (c := c) (db := db)
    (by rw [k5.get .x28, O4.cs .x28 (by decide), k3.get .x28, k2.get .x28, k1.get .x28, I.x28])
    (by rw [k5.get .x25, g4 .x25 (by decide), h25]) done₅ (by omega_using [hc, hfit, c2]) (by omega_using [hfit, c2]))
    fun u6 ⟨k6, x28₆, x10₆, m6⟩ => ⟨by rw [x10₆, hs1], ?_⟩
  have R6 : Rep u6.mem S _ := R5.frame (m' := u6.mem) (rs := [slotR F sDone])
    (by rw [m6]; exact frame_slot _ F sDone _) (L.slotS (by decide))
  refine ⟨k6.sp.trans (k5.sp.trans (O4.sp.trans (k3.sp.trans (k2.sp.trans (k1.sp.trans I.sp))))),
    k6.rd.trans (k5.rd.trans (O4.rd.trans (k3.rd.trans (k2.rd.trans (k1.rd.trans I.rd))))),
    k6.wr.trans (k5.wr.trans (O4.wr.trans (k3.wr.trans (k2.wr.trans (k1.wr.trans I.wr))))), fun r hr => ?_,
    fun r hr => (k6.vcs r hr).trans ((k5.vcs r hr).trans ((O4.vec r hr).trans ((k3.vcs r hr).trans
      ((k2.vcs r hr).trans ((k1.vcs r hr).trans (I.vec r hr)))))), x28₆, ?_, ?_, fun o ho₁ ho₂ => ?_⟩
  · have := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have h6 : r ∉ [Reg.x28, .x9, .x16, .x10] := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h5 : r ∉ [Reg.x9, .x10, .x11, .x12, .x13, .x14, .x15] := by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k6.gpr r h6, k5.gpr r h5, g4 r this]
  · rw [m6, Mem.readW_writeW_self64, hs1]
  · rw [m6]
    exact I.fr.trans ((f1.mono (by simp)).trans ((f2.mono (by simp)).trans ((f3.mono (by simp)).trans
      ((O4.fr.mono (by simp)).trans ((f5.mono (by simp)).trans ((frame_slot _ F sDone _).mono (by simp)))))))
  · -- The bytes of `EM`: `DB` with one more digest XORed in.
    have hV4 : u4.mem (off S o) = mixV V mk e (min (c * H.D) db) o := by
      rw [O4.em o ho₁ ho₂]
      simp (disch := omega_using [ho₂]) only [ctrV, updL, clr, ite_eq_right]
      exact I.em o ho₁ ho₂
    rw [R6 o (by omega_using [c2, c6, ho₂])]
    simp only [xorV]
    by_cases hx : e + c * H.D ≤ o ∧ o < e + c * H.D + min H.D (db - c * H.D)
    · rw [ite_eq_left hx, hV4]
      have hk : o - (e + c * H.D) < H.D := by omega_using [hx]
      rw [← off_add, byte_of_bytesAt (p := off S oDig) d4 hk]
      simp only [mixV]
      rw [ite_eq_right (by omega_using [hx]), ite_eq_left ⟨by omega_using [hx], by omega_using [hs1, hx]⟩, ← hmk,
          mgf1_getD hG _ (by omega_using [hx]), hGh, hGl]
      have e1 : o - e = H.D * c + (o - (e + c * H.D)) := by rw [Nat.mul_comm]; omega_using [hx]
      rw [e1, Nat.mul_add_div hD, Nat.div_eq_of_lt hk, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
    · rw [ite_eq_right hx, hV4]
      simp only [mixV]
      by_cases hy : e ≤ o ∧ o < e + min (c * H.D) db
      · rw [ite_eq_left hy, ite_eq_left ⟨hy.1, by omega_using [hs1, hy]⟩]
      · rw [ite_eq_right hy, ite_eq_right (by omega_using [hs1, hx, hy])]

/-- `DB ⊕= MGF1(H, dbLen)`, where `H` is the `hLen` bytes after `DB`. -/
theorem mgfXor_ok {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x) (hGl : G.len = H.D)
    (hG : Proof.Mgf1.Valid G) {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {e db : Nat} (hd : DbAt H.D e db) (h19 : t.gpr .x19 = off S oSt) (h21 : t.gpr .x21 = off S oDig)
    (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db) :
    WP isa (mgfXor H) t fun t' => t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25, .x26], t'.gpr r = t.gpr r) ∧
      (∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) ∧
      Frame (mgfWr F S) t.mem t'.mem ∧
      ∀ o, oEm ≤ o → o < oY →
        t'.mem (off S o) = mixV V (Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db) e db o := by
  have hD := hH.sizes.D0
  have hdb1 := hd.db1
  have hfit := hd.fit
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  generalize hmk : Spec.Mgf1.mgf1 G ((List.range H.D).map fun i => V (e + db + i)) db = mk
  unfold mgfXor st
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_movz fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_addSp (by decide) fun u₃ o₃ e₃ => ?_)
  refine wp_strx (by decide) (by rw [e₃, o₂.sp, o₁.sp, L.sp, BitVec.add_zero])
    (by rw [o₃.wr, o₂.wr, o₁.wr]; exact L.fst (by decide)) fun v m₄ => wp_nil ?_
  have hm : v.mem = t.mem.writeW (off F sDone) (0#64) := by
    rw [m₄.mem, o₃.get .x9, e₂, o₃.mem, o₂.mem, o₁.mem]; rfl
  have K : Keep [.x28, .x9, .x16] t v := (o₁.keep.trans (o₂.keep.trans (o₃.keep.trans m₄.keep))).mono
  have I0 : MgfI t F S V mk e db H.D 0 v := by
    refine ⟨K.sp, K.rd, K.wr, fun r hr => K.gpr r ?_, K.vcs, ?_, ?_, ?_, fun o ho₁ ho₂ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [m₄.gpr, o₃.get .x28, o₂.get .x28, e₁]; rfl
    · rw [hm, Mem.readW_writeW_self64, Nat.zero_mul]
    · rw [hm]; exact (frame_slot _ F sDone _).mono (by simp)
    · have R' : Rep v.mem S V := R.frame (by rw [hm]; exact frame_slot _ F sDone _) (L.slotS (by decide))
      rw [R' o (by omega_using [c2, c6, ho₂])]
      simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]
      rw [ite_eq_right (by omega_using [])]
  refine WP.loop (M := isa) (fun n w => ∃ c, n = db - c * H.D ∧ c * H.D < db ∧ MgfI t F S V mk e db H.D c w)
    ?_ (db - 0 * H.D) v ⟨0, rfl, by omega_using [hdb1], I0⟩
  rintro n w ⟨c, rfl, hc, I⟩
  subst hmk
  refine WP.mono (round_ok hH hGh hGl hG L hd h19 h21 h24 h25 I hc) fun w' ⟨hx, I'⟩ => ?_
  have hs1 : (c + 1) * H.D = c * H.D + H.D := Nat.succ_mul _ _
  by_cases h : (c + 1) * H.D < db
  · exact .inr ⟨by rw [eval_nonzero, hx, decide_eq_true h], _, by omega_using [hD, hs1, h], c + 1, rfl, h, I'⟩
  · refine .inl ⟨by rw [eval_nonzero, hx, decide_eq_false h], I'.sp, I'.rd, I'.wr, I'.cs, I'.vec, I'.fr,
      fun o ho₁ ho₂ => ?_⟩
    rw [I'.em o ho₁ ho₂, Nat.min_eq_right (by omega_using [h])]

end

end VG.Proof.RsaPss.AArch64
