import VerifiedGarbage.Proof.Sha256.X86.Stream.Base
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Impl.Sha512.X86
import VerifiedGarbage.Proof.Sha512.Spec

/-!
# x86 (32-bit): 64-bit words as pairs of 32-bit words

Weakest-precondition rules for the macros of `VG.Impl.Sha512.X86` that keep a
64-bit word in a pair of general-purpose registers (loads and stores of a
64-bit word in a buffer, 64-bit additions; BLAKE2b's, Argon2's and SHA-3's
x86 code use them) and for `loadW`, which makes a message word of SHA-512,
each proved once for any registers and offsets, in continuation-passing
style: the rule for `x` proves `WP (x ++ rest)` from a proof of `WP rest` for
every state `x` can end in. The halves of 64-bit values are those of
`Proof/Sha512/Word64.lean`.
-/

namespace VG.Proof.Sha512.X86

open VG VG.X86
open VG.Impl.Sha512.X86 (at_ sc T Y0 Y1 Z0 Z1 ld st add64 add64m loadW)
open VG.Proof.Sha512.Word64 (lo hi lo_add hi_add lo_append hi_append hi_append_lo)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd WP.cons wp_store wp_bswap wp_shr)

theorem lo_eq (x : BitVec 64) : Impl.Sha512.X86.lo x = lo x := rfl
theorem hi_eq (x : BitVec 64) : Impl.Sha512.X86.hi x = hi x := rfl

/-! ## States -/

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags). -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Only.refl (ds : List Reg) (s : State) : Only ds s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Only.of_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r h => u.other r (by simpa using h), u.mem, u.rd, u.wr⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃) :
    Only (ds ++ es) s₁ s₃ :=
  ⟨fun r h => by
    simp only [List.mem_append, not_or] at h
    rw [h₂.gpr r h.2, h₁.gpr r h.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    Only es s s' :=
  ⟨fun r hr => h.gpr r fun hd => hr (he r hd), h.mem, h.rd, h.wr⟩

/-- The 64-bit word `x` is in the registers `l` (low half) and `h`. -/
def Pair (s : State) (l h : Reg) (x : BitVec 64) : Prop := s.gpr l = lo x ∧ s.gpr h = hi x

theorem Pair.of_only {s s' : State} {l h : Reg} {x : BitVec 64} {ds : List Reg} (p : Pair s l h x)
    (o : Only ds s s') (hl : l ∉ ds) (hh : h ∉ ds) : Pair s' l h x :=
  ⟨(o.gpr l hl).trans p.1, (o.gpr h hh).trans p.2⟩

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags), and memory `m`. -/
structure Wrote (ds : List Reg) (s s' : State) (m : Mem) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Only.wrote {ds : List Reg} {s₁ s₂ s₃ : State} {m : Mem} (h : Only ds s₁ s₂) (u : Mupd s₂ s₃ m) :
    Wrote ds s₁ s₃ m :=
  ⟨fun r hr => by rw [u.gpr, h.gpr r hr], u.mem, u.rd.trans h.rd, u.wr.trans h.wr⟩

theorem Wrote.mono' {ds es : List Reg} {s s' : State} {m : Mem} (w : Wrote ds s s' m)
    (h : ∀ r ∈ ds, r ∈ es) : Wrote es s s' m :=
  ⟨fun r hr => w.gpr r fun hd => hr (h r hd), w.mem, w.rd, w.wr⟩

/-! ## Memory -/

/-- The 64-bit word at `[b + off]`, from its two halves. -/
def rd64 (m : Mem) (b : BitVec 32) (off : Nat) : BitVec 64 :=
  m.readW (addr b (off + 4)) 32 ++ m.readW (addr b off) 32

/-- Store the 64-bit word `x` at `[b + off]`, as its two halves. -/
def write64 (m : Mem) (b : BitVec 32) (off : Nat) (x : BitVec 64) : Mem :=
  (m.writeW (addr b off) (lo x)).writeW (addr b (off + 4)) (hi x)

theorem lo_rd64 (m : Mem) (b : BitVec 32) (off : Nat) : lo (rd64 m b off) = m.readW (addr b off) 32 :=
  lo_append _ _

theorem hi_rd64 (m : Mem) (b : BitVec 32) (off : Nat) :
    hi (rd64 m b off) = m.readW (addr b (off + 4)) 32 :=
  hi_append _ _

theorem mem_rd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Every word `[B + o, B + o + 4)` with `o + 4 ≤ N` is writable. -/
def Acc (wr : List Region) (B : BitVec 32) (N : Nat) : Prop :=
  ∀ o, o + 4 ≤ N → InRegions wr (addr B o) 4

/-! ## Single instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem ea_of {b : Reg} {B : BitVec 32} (hb : s.gpr b = B) (d : Nat) : s.ea (at_ b d) = addr B d := by
  rw [← hb]; rfl

theorem readSrc_mem {b : Reg} {d : Nat} {B : BitVec 32} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B d) 4) :
    readSrc s (.mem (at_ b d)) = some (s.mem.readW (addr B d) 32) := by
  show s.load32 (s.ea (at_ b d)) = _
  rw [ea_of hb]; simp only [State.load32, hin, ↓reduceIte]

theorem wp_movS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d src :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp [exec, h]) (k _ (Upd.setReg _ _ _))

theorem wp_addS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_adcS {d : Reg} {src : Src} {v : BitVec 32} {c : Bool} (h : readSrc s src = some v)
    (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h, hc]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xorS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_andS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_orS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d ||| v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_ror {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d ((s.gpr d).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q :=
  WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl)
    (k _ (Upd.setFlags _ _ _ _ _ _ _))

end

theorem carry_eq (a b : BitVec 32) :
    (BitVec.ofBool (decide (2 ^ 32 ≤ a.toNat + b.toNat))).setWidth 32 =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> rfl

/-- A left shift, as the code computes it: a rotation, masked. -/
theorem ror_and (x : BitVec 32) {n : Nat} (h0 : 0 < n) (h : n < 32) :
    x.rotateRight (32 - n) &&& (BitVec.allOnes 32 <<< n) = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, Nat.mod_eq_of_lt (show 32 - n < 32 by omega)]
  by_cases hc : i < n
  · simp [hc, hi]
  · simp [hc, hi, show ¬ i < 32 - (32 - n) by omega, show i - (32 - (32 - n)) = i - n by omega]
    omega

/-! ## Loads, stores and additions of 64-bit words in the scratch buffer -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_ld {l h : Reg} {B : BitVec 32} {off N : Nat} (hl : l ≠ .esi) (hlh : l ≠ h)
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N)
    (k : ∀ s', Only [l, h] s s' → Pair s' l h (rd64 s.mem B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ld l h off ++ rest)) s Q := by
  simp only [ld, sc, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem hb (mem_rd (hA off (by omega)))) fun s₁ u₁ => ?_
  refine wp_movS (readSrc_mem (by rw [u₁.other _ (Ne.symm hl), hb])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA (off + 4) (by omega)))) fun s₂ u₂ =>
    k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other l hlh, u₁.gpr, lo_rd64]
  · rw [u₂.gpr, u₁.mem, hi_rd64]

theorem wp_st {l h : Reg} {B : BitVec 32} {off N : Nat} {x : BitVec 64}
    (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N) (hp : Pair s l h x)
    (k : ∀ s', Mupd s s' (write64 s.mem B off x) → WP isa (.block rest) s' Q) :
    WP isa (.block (st l h off ++ rest)) s Q := by
  simp only [st, List.cons_append, List.nil_append]
  refine wp_store (ea_of hb _) (hA off (by omega)) fun s₁ u₁ => ?_
  refine wp_store (ea_of (by rw [u₁.gpr, hb]) _) (by rw [u₁.wr]; exact hA (off + 4) (by omega))
    fun s₂ u₂ => k s₂ ⟨u₂.gpr.trans u₁.gpr, ?_, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr⟩
  rw [u₂.mem, u₁.mem, u₁.gpr, hp.1, hp.2]; rfl

theorem wp_add64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : Pair s dl dh x) (py : Pair s l h y)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x + y) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64 dl dh l h ++ rest)) s Q := by
  simp only [add64, List.cons_append, List.nil_append]
  refine wp_addS rfl fun s₁ u₁ hc => ?_
  refine wp_adcS rfl hc fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, lo_add]
  · rw [u₂.gpr, carry_eq, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.1, py.1, px.2,
      py.2, hi_add]

theorem wp_add64m {dl dh : Reg} {x : BitVec 64} {B : BitVec 32} {off N : Nat} (h₁ : dl ≠ dh)
    (h₂ : dl ≠ .esi) (hb : s.gpr .esi = B) (hA : Acc s.wr B N) (ho : off + 8 ≤ N) (px : Pair s dl dh x)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x + rd64 s.mem B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64m dl dh off ++ rest)) s Q := by
  simp only [add64m, sc, List.cons_append, List.nil_append]
  refine wp_addS (readSrc_mem hb (mem_rd (hA off (by omega)))) fun s₁ u₁ hc => ?_
  refine wp_adcS (readSrc_mem (by rw [u₁.other _ (Ne.symm h₂), hb])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA (off + 4) (by omega)))) hc fun s₂ u₂ =>
    k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, lo_add, lo_rd64]
  · rw [u₂.gpr, carry_eq, u₁.other dh (Ne.symm h₁), u₁.mem, px.1, px.2, hi_add, lo_rd64, hi_rd64]

end

/-! ## 64-bit words in memory -/

open VG.Proof.Sha256.X86.Stream (readW_writeW_addr) in
theorem rd64_write64_self (m : Mem) {b : BitVec 32} {o : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) : rd64 (write64 m b o x) b o = x := by
  simp only [rd64, write64]
  rw [Mem.readW_writeW_self32, readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    Mem.readW_writeW_self32, hi_append_lo]

open VG.Proof.Sha256.X86.Stream (readW_writeW_addr) in
theorem rd64_write64_ne (m : Mem) {b : BitVec 32} {o o' : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) (h' : b.toNat + o' + 8 ≤ 2 ^ 32) (hs : o + 8 ≤ o' ∨ o' + 8 ≤ o) :
    rd64 (write64 m b o x) b o' = rd64 m b o' := by
  simp only [rd64, write64]
  rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega)]

/-! ## The message schedule -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_loadW {i o N : Nat} {Bb B : BitVec 32} (ho : o + 8 ≤ N)
    (hA : Acc s.wr B N) (hb : s.gpr .esi = B) (hbb : s.gpr .edi = Bb)
    (hin : InRegions (s.rd ++ s.wr) (addr Bb i) 4) (hin' : InRegions (s.rd ++ s.wr) (addr Bb (i + 4)) 4)
    (k : ∀ s', Wrote [Z0, Z1] s s' (write64 s.mem B o
      (bswap (s.mem.readW (addr Bb i) 32) ++ bswap (s.mem.readW (addr Bb (i + 4)) 32))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loadW i o ++ rest)) s Q := by
  simp only [loadW, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_mem hbb hin') fun s₁ u₁ => ?_
  refine wp_movS (readSrc_mem (by rw [u₁.other _ (by decide), hbb]) (by rw [u₁.rd, u₁.wr]; exact hin))
    fun s₂ u₂ => wp_bswap fun s₃ u₃ => wp_bswap fun s₄ u₄ => ?_
  have O := (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  refine wp_st (x := bswap (s.mem.readW (addr Bb i) 32) ++ bswap (s.mem.readW (addr Bb (i + 4)) 32))
    (by rw [O.gpr _ (by decide), hb]) (by rw [O.wr]; exact hA) ho ⟨?_, ?_⟩ fun s₅ u₅ => k s₅ ?_
  · rw [lo_append, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr]
  · rw [hi_append, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.mem]
  · rw [O.mem] at u₅
    exact (O.mono (by decide)).wrote u₅

end

open VG.Proof.Sha256.X86.Stream (contains_addr)

theorem frame_write64 {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hr : ⟨b.setWidth 64, N⟩ ∈ rs) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) (x : BitVec 64) :
    Frame rs m (write64 m' b o x) :=
  (h.writeW hr _ (contains_addr (by omega) (by omega) hfit)).writeW hr _
    (contains_addr (by omega) (by omega) hfit)

theorem Acc.of_mem {wr : List Region} {B : BitVec 32} {N : Nat} (h : ⟨B.setWidth 64, N⟩ ∈ wr)
    (hfit : B.toNat + N ≤ 2 ^ 32) : Acc wr B N :=
  fun _ ho => ⟨_, h, contains_addr ho (by omega) hfit⟩

theorem rd64_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b.setWidth 64, N⟩ r) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) :
    rd64 m' b o = rd64 m b o := by
  simp only [rd64]
  rw [h.readW (contains_addr (by omega) (by omega) hfit) hd (by decide),
    h.readW (contains_addr (by omega) (by omega) hfit) hd (by decide)]

end VG.Proof.Sha512.X86
