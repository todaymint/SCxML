-- Light Puzzle: n×n×n Cube of Lamps
-- Theory and Proofs

namespace LightPuzzle

/-! ## Basic Definitions -/

-- Direction of the line (X, Y, or Z axis)
inductive Direction
  | x
  | y
  | z
  deriving DecidableEq, Repr

-- Represents the configuration of lamps (1 = on, 0 = off)
def Config (_n : Nat) := List (List (List Nat))

-- A move: pressing a square on a surface
structure Move (n : Nat) where
  dir : Direction
  u : Nat
  v : Nat
  deriving DecidableEq

/-! ## Helper Functions -/

def listGet (lst : List α) (idx : Nat) (default : α) : α :=
  match lst with
  | [] => default
  | h :: t => if idx = 0 then h else listGet t (idx - 1) default

def listSet (lst : List α) (idx : Nat) (val : α) : List α :=
  match lst with
  | [] => []
  | h :: t => if idx = 0 then val :: t else h :: listSet t (idx - 1) val

def getLight (n : Nat) (config : Config n) (x y z : Nat) : Nat :=
  if x < n ∧ y < n ∧ z < n then
    let layer := listGet config x []
    let row := listGet layer y []
    listGet row z 0
  else 0

def updateList1D (lst : List Nat) (idx : Nat) (f : Nat → Nat) : List Nat :=
  listSet lst idx (f (listGet lst idx 0))

def updateList2D (lst : List (List Nat)) (y z : Nat) (f : Nat → Nat) : List (List Nat) :=
  listSet lst y (updateList1D (listGet lst y []) z f)

def updateList3D (lst : List (List (List Nat))) (x y z : Nat) (f : Nat → Nat) :
    List (List (List Nat)) :=
  listSet lst x (updateList2D (listGet lst x []) y z f)

def setLight (n : Nat) (config : Config n) (x y z : Nat) (val : Nat) : Config n :=
  if x < n ∧ y < n ∧ z < n then
    updateList3D config x y z (fun _ => val)
  else config

def toggleLight (n : Nat) (config : Config n) (x y z : Nat) : Config n :=
  let current := getLight n config x y z
  setLight n config x y z ((current + 1) % 2)

abbrev Coord := Nat × Nat × Nat

def toggleAt (n : Nat) (config : Config n) (coord : Coord) : Config n :=
  toggleLight n config coord.1 coord.2.1 coord.2.2

def isAllOff (n : Nat) (config : Config n) : Bool :=
  config.all fun layer =>
    layer.all fun row =>
      row.all fun light => light = 0

-- Prop version: every lamp is off
def IsAllOff (n : Nat) (config : Config n) : Prop :=
  ∀ x y z, x < n → y < n → z < n → getLight n config x y z = 0

-- Well-formedness: config has correct dimensions and values in {0,1}
def WellFormed (n : Nat) (config : Config n) : Prop :=
  (config : List _).length = n ∧
  (∀ i, i < n → (listGet (config : List _) i []).length = n) ∧
  (∀ i j, i < n → j < n → (listGet (listGet (config : List _) i []) j []).length = n) ∧
  (∀ i j k, i < n → j < n → k < n →
    listGet (listGet (listGet (config : List _) i []) j []) k 0 < 2)

-- Proof-facing wrapper: a configuration together with the legality invariant.
structure ValidConfig (n : Nat) where
  data : Config n
  wf : WellFormed n data

/-! ## Move Operations -/

def applyMove (n : Nat) (move : Move n) (config : Config n) : Config n :=
  match move.dir with
  | Direction.x =>
      (List.range n).foldl (fun cfg i => toggleLight n cfg i move.u move.v) config
  | Direction.y =>
      (List.range n).foldl (fun cfg j => toggleLight n cfg move.u j move.v) config
  | Direction.z =>
      (List.range n).foldl (fun cfg k => toggleLight n cfg move.u move.v k) config

private def flatMap (f : α → List β) : List α → List β
  | [] => []
  | h :: t => f h ++ flatMap f t

-- Apply a list of moves sequentially
def applyMoves (n : Nat) (moves : List (Move n)) (config : Config n) : Config n :=
  moves.foldl (fun cfg m => applyMove n m cfg) config

-- A configuration is solvable iff there exists a list of moves turning all lights off
def IsSolvable (n : Nat) (config : Config n) : Prop :=
  ∃ moves : List (Move n), IsAllOff n (applyMoves n moves config)

def allMoves (n : Nat) : List (Move n) :=
  flatMap (fun u =>
    flatMap (fun v =>
      [⟨Direction.x, u, v⟩, ⟨Direction.y, u, v⟩, ⟨Direction.z, u, v⟩])
      (List.range n))
    (List.range n)

/-! ## Examples -/

def configExample1 : Config 3 :=
  [[[1, 0, 1], [0, 1, 0], [1, 0, 1]],
   [[0, 1, 0], [1, 0, 1], [0, 1, 0]],
   [[1, 0, 1], [0, 1, 0], [1, 0, 1]]]

def configExample2 : Config 3 :=
  [[[1, 1, 1], [1, 1, 0], [1, 0, 0]],
   [[0, 1, 0], [0, 1, 1], [0, 0, 1]],
   [[1, 0, 0], [1, 0, 1], [0, 0, 0]]]

def makeAllOff (n : Nat) : Config n :=
  (List.range n).map fun _ =>
    (List.range n).map fun _ =>
      List.range n |>.map fun _ => 0

def makeAllOn (n : Nat) : Config n :=
  (List.range n).map fun _ =>
    (List.range n).map fun _ =>
      List.range n |>.map fun _ => 1

def allOff₃ : Config 3 := makeAllOff 3
def allOn₃ : Config 3 := makeAllOn 3

/-! ## Pretty Print -/

private def lampToString (x : Nat) : String :=
  if x = 0 then "·" else "●"

private def rowToString (row : List Nat) : String :=
  "[" ++ String.intercalate ", " (row.map lampToString) ++ "]"

private def natToString (n : Nat) : String :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | n + 1 => natToString (n / 10) ++ natToString (n % 10)

private def zHeader (size : Nat) : String :=
  "       " ++ String.intercalate "  " ((List.range size).map (fun i => "z" ++ natToString i))

private def layerToString (_size : Nat) (layer : List (List Nat)) : String :=
  String.intercalate "\n" (
    layer.mapIdx fun j row =>
      "  y" ++ natToString j ++ "  " ++ rowToString row
  )

def configToString (n : Nat) (config : Config n) : String :=
  zHeader n ++ "\n" ++
  String.intercalate "\n" (
    config.mapIdx fun i layer =>
      "X-face " ++ natToString i ++ ":\n" ++ layerToString n layer
  )

def prettyPrint (n : Nat) (config : Config n) : String :=
  "Light Puzzle Configuration (n=" ++ natToString n ++ "):\n" ++
  configToString n config ++ "\n" ++
  (if isAllOff n config then "All lights are OFF" else "Some lights are ON")

/-! ## Core Algorithm -/

-- Generic surface processing: given a direction, look at the "front face"
-- (coordinate 0 in that direction) and press every lit square.
def processSurface (n : Nat) (dir : Direction) (config : Config n) : Config n :=
  (List.range n).foldl (fun cfg₁ u =>
    (List.range n).foldl (fun cfg₂ v =>
      let lit := match dir with
        | Direction.x => getLight n cfg₂ 0 u v
        | Direction.y => getLight n cfg₂ u 0 v
        | Direction.z => getLight n cfg₂ u v 0
      if lit = 1 then
        applyMove n ⟨dir, u, v⟩ cfg₂
      else cfg₂)
    cfg₁)
    config

-- The three surface operations are instances of processSurface
def processXSurface (n : Nat) (config : Config n) : Config n :=
  processSurface n Direction.x config

def processYSurface (n : Nat) (config : Config n) : Config n :=
  processSurface n Direction.y config

def processZSurface (n : Nat) (config : Config n) : Config n :=
  processSurface n Direction.z config

def greedyAlgorithm (n : Nat) (config : Config n) : Config n :=
  processZSurface n (processYSurface n (processXSurface n config))

def isSolvableByAlgorithm (n : Nat) (config : Config n) : Bool :=
  isAllOff n (greedyAlgorithm n config)

def processSurfaceInnerTraceStep (n : Nat) (dir : Direction) (u : Nat)
    (acc : Config n × List (Move n)) (v : Nat) : Config n × List (Move n) :=
  let cfg := acc.1
  let moves := acc.2
  let lit := match dir with
    | Direction.x => getLight n cfg 0 u v
    | Direction.y => getLight n cfg u 0 v
    | Direction.z => getLight n cfg u v 0
  if lit = 1 then
    let move : Move n := ⟨dir, u, v⟩
    (applyMove n move cfg, moves ++ [move])
  else
    acc

def processSurfaceTraceStep (n : Nat) (dir : Direction)
    (acc : Config n × List (Move n)) (u : Nat) : Config n × List (Move n) :=
  (List.range n).foldl (processSurfaceInnerTraceStep n dir u) acc

def processSurfaceTrace (n : Nat) (dir : Direction) (config : Config n) : Config n × List (Move n) :=
  (List.range n).foldl (processSurfaceTraceStep n dir) (config, [])

def greedyAlgorithmTrace (n : Nat) (config : Config n) : Config n × List (Move n) :=
  let xTrace := processSurfaceTrace n Direction.x config
  let yTrace := processSurfaceTrace n Direction.y xTrace.1
  let zTrace := processSurfaceTrace n Direction.z yTrace.1
  (zTrace.1, xTrace.2 ++ yTrace.2 ++ zTrace.2)

/-! ## Helper Lemmas for listGet / listSet -/

theorem listGet_listSet_same (lst : List α) (idx : Nat) (val default : α)
    (h : idx < lst.length) :
    listGet (listSet lst idx val) idx default = val := by
  induction lst generalizing idx with
  | nil => simp [List.length] at h
  | cons hd tl ih =>
    simp only [listSet]
    cases Nat.decEq idx 0 with
    | isTrue he => subst he; simp [listGet]
    | isFalse hne =>
      simp [hne, listGet]
      apply ih; simp [List.length] at h; omega

theorem listSet_listSet_same (lst : List α) (idx : Nat) (v1 v2 : α) :
    listSet (listSet lst idx v1) idx v2 = listSet lst idx v2 := by
  induction lst generalizing idx with
  | nil => simp [listSet]
  | cons hd tl ih =>
    simp only [listSet]
    cases Nat.decEq idx 0 with
    | isTrue he => subst he; simp [listSet]
    | isFalse hne => simp [hne, listSet, ih]

theorem listGet_listSet_diff (lst : List α) (i j : Nat) (val default : α)
    (hne : i ≠ j) :
    listGet (listSet lst j val) i default = listGet lst i default := by
  induction lst generalizing i j with
  | nil => simp [listSet, listGet]
  | cons hd tl ih =>
    simp only [listSet, listGet]
    cases Nat.decEq j 0 with
    | isTrue hj =>
      subst hj
      cases Nat.decEq i 0 with
      | isTrue hi => exact absurd hi hne
      | isFalse _ => simp [*, listGet]
    | isFalse hj =>
      simp [hj]
      cases Nat.decEq i 0 with
      | isTrue hi => subst hi; simp [listGet]
      | isFalse hi => simp [hi, listGet]; apply ih; omega

theorem listSet_length (lst : List α) (idx : Nat) (val : α) :
    (listSet lst idx val).length = lst.length := by
  induction lst generalizing idx with
  | nil => simp [listSet]
  | cons hd tl ih =>
    simp only [listSet]
    cases Nat.decEq idx 0 with
    | isTrue he => subst he; simp [List.length]
    | isFalse hne => simp [hne, List.length, ih]

-- If every element of a list satisfies a Bool predicate, then listGet also does.
-- The default case is handled by requiring the predicate on the default value.
theorem listGet_all_eq_true (lst : List α) (idx : Nat) (default : α) (p : α → Bool)
  (hall : lst.all p = true) (hdefault : p default = true) :
  p (listGet lst idx default) = true := by
  induction lst generalizing idx with
  | nil =>
    simp [listGet, hdefault]
  | cons hd tl ih =>
    have hall' : ∀ x, x ∈ hd :: tl → p x = true := List.all_eq_true.mp hall
    cases idx with
    | zero =>
        simpa [listGet] using hall' hd (by simp)
    | succ idx =>
        have htl : tl.all p = true := by
          apply List.all_eq_true.mpr
          intro a ha
          exact hall' a (by simp [ha])
        simpa [listGet] using ih idx htl

theorem listGet_eq_get (lst : List α) (idx : Nat) (default : α) (h : idx < lst.length) :
    listGet lst idx default = lst.get ⟨idx, h⟩ := by
  induction lst generalizing idx with
  | nil =>
      cases h
  | cons hd tl ih =>
      cases idx with
      | zero =>
          simp [listGet]
      | succ idx =>
        simp [listGet]
        exact ih idx (by simpa using h)

theorem list_ext_get (l₁ l₂ : List α)
    (hlen : l₁.length = l₂.length)
    (hget : ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length),
      l₁.get ⟨i, h₁⟩ = l₂.get ⟨i, h₂⟩) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons hd tl => cases hlen
  | cons hd tl ih =>
      cases l₂ with
      | nil => cases hlen
      | cons hd₂ tl₂ =>
          have hHead : hd = hd₂ := by
            have h0₂ : 0 < (hd₂ :: tl₂).length := by
              simp
            exact hget 0 (by simp) h0₂
          have hTailLen : tl.length = tl₂.length := by
            simpa using Nat.succ.inj hlen
          have hTailGet : ∀ i (h₁ : i < tl.length) (h₂ : i < tl₂.length),
              tl.get ⟨i, h₁⟩ = tl₂.get ⟨i, h₂⟩ := by
            intro i h₁ h₂
            have hs₁ : i + 1 < (hd :: tl).length := by
              simp [h₁]
            have hs₂ : i + 1 < (hd₂ :: tl₂).length := by
              simp [h₂]
            exact hget (i + 1) hs₁ hs₂
          subst hd₂
          simp [ih tl₂ hTailLen hTailGet]

      theorem applyMoves_append (n : Nat) (moves₁ moves₂ : List (Move n)) (config : Config n) :
        applyMoves n (moves₁ ++ moves₂) config = applyMoves n moves₂ (applyMoves n moves₁ config) := by
        induction moves₁ generalizing config with
        | nil =>
          simp [applyMoves]
        | cons move moves ih =>
          simp [applyMoves]

      theorem processSurfaceInnerTrace_sound (n : Nat) (dir : Direction) (init : Config n)
        (u : Nat) (cols : List Nat) (cfg : Config n) (moves : List (Move n))
        (hcfg : applyMoves n moves init = cfg) :
        applyMoves n (((cols.foldl (processSurfaceInnerTraceStep n dir u) (cfg, moves)).2)) init =
          ((cols.foldl (processSurfaceInnerTraceStep n dir u) (cfg, moves)).1) := by
        induction cols generalizing cfg moves with
        | nil =>
          simpa using hcfg
        | cons v cols ih =>
            by_cases hlit :
                (match dir with
                  | Direction.x => getLight n cfg 0 u v
                  | Direction.y => getLight n cfg u 0 v
                  | Direction.z => getLight n cfg u v 0) = 1
            · simp [processSurfaceInnerTraceStep, hlit]
              apply ih
              rw [applyMoves_append, hcfg]
              simp [applyMoves]
            · simp [processSurfaceInnerTraceStep, hlit]
              exact ih cfg moves hcfg

        theorem processSurfaceTrace_sound_aux (n : Nat) (dir : Direction) (init : Config n)
          (rows : List Nat) (cfg : Config n) (moves : List (Move n))
          (hcfg : applyMoves n moves init = cfg) :
          applyMoves n ((rows.foldl (processSurfaceTraceStep n dir) (cfg, moves)).2) init =
            (rows.foldl (processSurfaceTraceStep n dir) (cfg, moves)).1 := by
          induction rows generalizing cfg moves with
          | nil =>
            simpa using hcfg
          | cons u rows ih =>
            simpa [processSurfaceTraceStep] using
            ih _ _ (processSurfaceInnerTrace_sound n dir init u (List.range n) cfg moves hcfg)

        theorem processSurfaceTrace_sound (n : Nat) (dir : Direction) (config : Config n) :
          applyMoves n (processSurfaceTrace n dir config).2 config = (processSurfaceTrace n dir config).1 := by
          unfold processSurfaceTrace
          simpa [applyMoves] using
          processSurfaceTrace_sound_aux n dir config (List.range n) config [] (by simp [applyMoves])

        theorem processSurfaceInnerTrace_fst (n : Nat) (dir : Direction) (u : Nat)
          (cols : List Nat) (cfg : Config n) (moves : List (Move n)) :
          (cols.foldl (processSurfaceInnerTraceStep n dir u) (cfg, moves)).1 =
            cols.foldl (fun cfg v =>
            let lit := match dir with
              | Direction.x => getLight n cfg 0 u v
              | Direction.y => getLight n cfg u 0 v
              | Direction.z => getLight n cfg u v 0
            if lit = 1 then applyMove n ⟨dir, u, v⟩ cfg else cfg) cfg := by
          induction cols generalizing cfg moves with
          | nil =>
            rfl
          | cons v cols ih =>
              by_cases hlit :
                  (match dir with
                    | Direction.x => getLight n cfg 0 u v
                    | Direction.y => getLight n cfg u 0 v
                    | Direction.z => getLight n cfg u v 0) = 1
              · simp [processSurfaceInnerTraceStep, hlit]
                simpa using ih (applyMove n ⟨dir, u, v⟩ cfg) (moves ++ [⟨dir, u, v⟩])
              · simp [processSurfaceInnerTraceStep, hlit]
                simpa using ih cfg moves

      theorem processSurfaceTrace_fst_aux (n : Nat) (dir : Direction)
          (rows : List Nat) (cfg : Config n) (moves : List (Move n)) :
          (rows.foldl (processSurfaceTraceStep n dir) (cfg, moves)).1 =
            List.foldl (fun cfg₁ u =>
              (List.range n).foldl (fun cfg₂ v =>
                let lit := match dir with
                  | Direction.x => getLight n cfg₂ 0 u v
                  | Direction.y => getLight n cfg₂ u 0 v
                  | Direction.z => getLight n cfg₂ u v 0
                if lit = 1 then applyMove n ⟨dir, u, v⟩ cfg₂ else cfg₂) cfg₁) cfg rows := by
        induction rows generalizing cfg moves with
        | nil =>
            rfl
        | cons u rows ih =>
            simp [processSurfaceTraceStep, processSurfaceInnerTrace_fst, ih]

      theorem processSurfaceTrace_fst (n : Nat) (dir : Direction) (config : Config n) :
          (processSurfaceTrace n dir config).1 = processSurface n dir config := by
        unfold processSurfaceTrace processSurface
        simpa using processSurfaceTrace_fst_aux n dir (List.range n) config []

      theorem greedyAlgorithmTrace_sound (n : Nat) (config : Config n) :
        applyMoves n (greedyAlgorithmTrace n config).2 config = (greedyAlgorithmTrace n config).1 := by
        unfold greedyAlgorithmTrace
        rw [applyMoves_append, applyMoves_append]
        rw [processSurfaceTrace_sound]
        rw [processSurfaceTrace_sound]
        rw [processSurfaceTrace_sound]

      theorem greedyAlgorithmTrace_fst (n : Nat) (config : Config n) :
        (greedyAlgorithmTrace n config).1 = greedyAlgorithm n config := by
        unfold greedyAlgorithmTrace greedyAlgorithm
        rw [processSurfaceTrace_fst, processSurfaceTrace_fst, processSurfaceTrace_fst]
        rfl

/-! ## Lemmas for getLight / setLight -/

-- setLight unfolds to a triple listSet
theorem setLight_unfold (n : Nat) (config : Config n) (x y z val : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n) :
    setLight n config x y z val =
    listSet config x (listSet (listGet config x []) y
      (listSet (listGet (listGet config x []) y []) z val)) := by
  simp [setLight, hx, hy, hz, updateList3D, updateList2D, updateList1D]

-- getLight after setLight at the same position = val
theorem getLight_setLight_same (n : Nat) (config : Config n) (x y z val : Nat)
    (wf : WellFormed n config) (hx : x < n) (hy : y < n) (hz : z < n) :
    getLight n (setLight n config x y z val) x y z = val := by
  rw [setLight_unfold n config x y z val hx hy hz]
  simp only [getLight, hx, hy, hz, and_self, ite_true]
  have h1 : x < (config : List _).length := by rw [wf.1]; exact hx
  have h2 : y < (listGet (config : List _) x []).length := by rw [wf.2.1 x hx]; exact hy
  have h3 : z < (listGet (listGet (config : List _) x []) y []).length := by
    rw [wf.2.2.1 x y hx hy]; exact hz
  rw [listGet_listSet_same _ x _ _ h1]
  rw [listGet_listSet_same _ y _ _ h2]
  rw [listGet_listSet_same _ z _ _ h3]

-- getLight after setLight at a different position = original
theorem getLight_setLight_diff (n : Nat) (config : Config n)
    (x y z x' y' z' val : Nat)
    (wf : WellFormed n config)
    (hne : ¬(x = x' ∧ y = y' ∧ z = z')) :
    getLight n (setLight n config x y z val) x' y' z' = getLight n config x' y' z' := by
  by_cases hb : x < n ∧ y < n ∧ z < n
  · obtain ⟨hx, hy, hz⟩ := hb
    rw [setLight_unfold n config x y z val hx hy hz]
    simp only [getLight]
    have h1 : x < (config : List _).length := by rw [wf.1]; exact hx
    have h2 : y < (listGet (config : List _) x []).length := by rw [wf.2.1 x hx]; exact hy
    by_cases hb' : x' < n ∧ y' < n ∧ z' < n
    · simp only [if_pos hb']
      by_cases hxx : x = x'
      · subst hxx
        rw [listGet_listSet_same _ x _ _ h1]
        have hyz : ¬(y = y' ∧ z = z') := fun ⟨hy, hz⟩ => hne ⟨rfl, hy, hz⟩
        by_cases hyy : y = y'
        · subst hyy
          rw [listGet_listSet_same _ y _ _ h2]
          rw [listGet_listSet_diff _ z' z _ _ (fun h => hyz ⟨rfl, h.symm⟩)]
        · rw [listGet_listSet_diff _ y' y _ _ (Ne.symm hyy)]
      · rw [listGet_listSet_diff _ x' x _ _ (Ne.symm hxx)]
    · simp only [if_neg hb']
  · simp only [setLight, if_neg hb]

theorem bit_flip_involutive {a : Nat} (ha : a < 2) : (((a + 1) % 2) + 1) % 2 = a := by
  have hCases : a = 0 ∨ a = 1 := by omega
  cases hCases with
  | inl h0 => simp [h0]
  | inr h1 => simp [h1]

theorem setLight_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z val : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n) (hval : val < 2) :
    WellFormed n (setLight n config x y z val) := by
  rw [setLight_unfold n config x y z val hx hy hz]
  rcases wf with ⟨hLen, hLayerLen, hRowLen, hBits⟩
  constructor
  · rw [listSet_length, hLen]
  constructor
  · intro i hi
    by_cases hix : i = x
    · subst hix
      rw [listGet_listSet_same _ i _ _ (by simpa [hLen] using hi)]
      rw [listSet_length, hLayerLen i hi]
    · rw [listGet_listSet_diff _ i x _ _ hix]
      exact hLayerLen i hi
  constructor
  · intro i j hi hj
    by_cases hix : i = x
    · subst hix
      rw [listGet_listSet_same _ i _ _ (by simpa [hLen] using hi)]
      by_cases hjy : j = y
      · subst hjy
        rw [listGet_listSet_same _ j _ _ (by simpa [hLayerLen i hi] using hj)]
        rw [listSet_length, hRowLen i j hi hj]
      · rw [listGet_listSet_diff _ j y _ _ hjy]
        exact hRowLen i j hi hj
    · rw [listGet_listSet_diff _ i x _ _ hix]
      exact hRowLen i j hi hj
  · intro i j k hi hj hk
    by_cases hix : i = x
    · subst hix
      rw [listGet_listSet_same _ i _ _ (by simpa [hLen] using hi)]
      by_cases hjy : j = y
      · subst hjy
        rw [listGet_listSet_same _ j _ _ (by simpa [hLayerLen i hi] using hj)]
        by_cases hkz : k = z
        · subst hkz
          rw [listGet_listSet_same _ k _ _ (by simpa [hRowLen i j hi hj] using hk)]
          exact hval
        · rw [listGet_listSet_diff _ k z _ _ hkz]
          exact hBits i j k hi hj hk
      · rw [listGet_listSet_diff _ j y _ _ hjy]
        exact hBits i j k hi hj hk
    · rw [listGet_listSet_diff _ i x _ _ hix]
      exact hBits i j k hi hj hk

theorem toggleLight_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n) :
    WellFormed n (toggleLight n config x y z) := by
  unfold toggleLight
  apply setLight_preserves_WellFormed n config wf x y z (((getLight n config x y z) + 1) % 2) hx hy hz
  omega

theorem getLight_toggleLight_same (n : Nat) (config : Config n) (x y z : Nat)
    (wf : WellFormed n config) (hx : x < n) (hy : y < n) (hz : z < n) :
    getLight n (toggleLight n config x y z) x y z = ((getLight n config x y z) + 1) % 2 := by
  unfold toggleLight
  exact getLight_setLight_same n config x y z (((getLight n config x y z) + 1) % 2) wf hx hy hz

theorem getLight_toggleLight_diff (n : Nat) (config : Config n)
    (x y z x' y' z' : Nat) (wf : WellFormed n config)
    (hne : ¬(x = x' ∧ y = y' ∧ z = z')) :
    getLight n (toggleLight n config x y z) x' y' z' = getLight n config x' y' z' := by
  unfold toggleLight
  exact getLight_setLight_diff n config x y z x' y' z' (((getLight n config x y z) + 1) % 2) wf hne

theorem config_ext (n : Nat) (config₁ config₂ : Config n)
    (wf₁ : WellFormed n config₁) (wf₂ : WellFormed n config₂)
    (h : ∀ x y z, x < n → y < n → z < n →
      getLight n config₁ x y z = getLight n config₂ x y z) :
    config₁ = config₂ := by
  apply list_ext_get config₁ config₂ (wf₁.1.trans wf₂.1.symm)
  intro x hx₁ hx₂
  have hx : x < n := by simpa [wf₁.1] using hx₁
  have hLayerLen₁ : (config₁.get ⟨x, hx₁⟩).length = n := by
    have hLen := wf₁.2.1 x hx
    rw [listGet_eq_get config₁ x [] hx₁] at hLen
    exact hLen
  have hLayerLen₂ : (config₂.get ⟨x, hx₂⟩).length = n := by
    have hLen := wf₂.2.1 x (by simpa [wf₂.1] using hx₂)
    rw [listGet_eq_get config₂ x [] hx₂] at hLen
    exact hLen
  apply list_ext_get (config₁.get ⟨x, hx₁⟩) (config₂.get ⟨x, hx₂⟩) (hLayerLen₁.trans hLayerLen₂.symm)
  intro y hy₁ hy₂
  have hy : y < n := by rw [hLayerLen₁] at hy₁; exact hy₁
  have hRowLen₁ : ((config₁.get ⟨x, hx₁⟩).get ⟨y, hy₁⟩).length = n := by
    have hLen := wf₁.2.2.1 x y hx hy
    rw [listGet_eq_get config₁ x [] hx₁] at hLen
    rw [listGet_eq_get (config₁.get ⟨x, hx₁⟩) y [] hy₁] at hLen
    exact hLen
  have hRowLen₂ : ((config₂.get ⟨x, hx₂⟩).get ⟨y, hy₂⟩).length = n := by
    have hLen := wf₂.2.2.1 x y (by simpa [wf₂.1] using hx₂) (by rw [hLayerLen₂] at hy₂; exact hy₂)
    rw [listGet_eq_get config₂ x [] hx₂] at hLen
    rw [listGet_eq_get (config₂.get ⟨x, hx₂⟩) y [] hy₂] at hLen
    exact hLen
  apply list_ext_get ((config₁.get ⟨x, hx₁⟩).get ⟨y, hy₁⟩) ((config₂.get ⟨x, hx₂⟩).get ⟨y, hy₂⟩)
    (hRowLen₁.trans hRowLen₂.symm)
  intro z hz₁ hz₂
  have hz : z < n := by rw [hRowLen₁] at hz₁; exact hz₁
  have hxyz := h x y z hx hy hz
  simp [getLight, hx, hy, hz] at hxyz
  rw [listGet_eq_get config₁ x [] hx₁] at hxyz
  rw [listGet_eq_get (config₁.get ⟨x, hx₁⟩) y [] hy₁] at hxyz
  rw [listGet_eq_get ((config₁.get ⟨x, hx₁⟩).get ⟨y, hy₁⟩) z 0 hz₁] at hxyz
  rw [listGet_eq_get config₂ x [] hx₂] at hxyz
  rw [listGet_eq_get (config₂.get ⟨x, hx₂⟩) y [] hy₂] at hxyz
  rw [listGet_eq_get ((config₂.get ⟨x, hx₂⟩).get ⟨y, hy₂⟩) z 0 hz₂] at hxyz
  exact hxyz

theorem toggleLight_involutive (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n) :
    toggleLight n (toggleLight n config x y z) x y z = config := by
  have hfirstWf : WellFormed n (toggleLight n config x y z) :=
    toggleLight_preserves_WellFormed n config wf x y z hx hy hz
  have hsecondWf : WellFormed n (toggleLight n (toggleLight n config x y z) x y z) :=
    toggleLight_preserves_WellFormed n (toggleLight n config x y z) hfirstWf x y z hx hy hz
  apply config_ext n (toggleLight n (toggleLight n config x y z) x y z) config hsecondWf wf
  intro x' y' z' hx' hy' hz'
  by_cases hsame : x' = x ∧ y' = y ∧ z' = z
  · rcases hsame with ⟨hxEq, hyEq, hzEq⟩
    subst x'
    subst y'
    subst z'
    simp [toggleLight]
    rw [getLight_setLight_same n config x y z (((getLight n config x y z) + 1) % 2) wf hx hy hz]
    rw [getLight_setLight_same n (setLight n config x y z (((getLight n config x y z) + 1) % 2)) x y z
      (((((getLight n config x y z) + 1) % 2) + 1) % 2) hfirstWf hx hy hz]
    exact bit_flip_involutive (by simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz)
  · have hne : ¬(x = x' ∧ y = y' ∧ z = z') := by
      intro hxyz
      apply hsame
      exact ⟨hxyz.1.symm, hxyz.2.1.symm, hxyz.2.2.symm⟩
    simp [toggleLight]
    rw [getLight_setLight_diff n (setLight n config x y z (((getLight n config x y z) + 1) % 2))
      x y z x' y' z' ((getLight n (setLight n config x y z (((getLight n config x y z) + 1) % 2)) x y z + 1) % 2)
      hfirstWf hne]
    rw [getLight_setLight_diff n config x y z x' y' z' (((getLight n config x y z) + 1) % 2) wf hne]

theorem toggleLight_comm (n : Nat) (config : Config n)
    (x₁ y₁ z₁ x₂ y₂ z₂ : Nat)
    (wf : WellFormed n config)
    (hx₁ : x₁ < n) (hy₁ : y₁ < n) (hz₁ : z₁ < n)
    (hx₂ : x₂ < n) (hy₂ : y₂ < n) (hz₂ : z₂ < n) :
    toggleLight n (toggleLight n config x₁ y₁ z₁) x₂ y₂ z₂ =
    toggleLight n (toggleLight n config x₂ y₂ z₂) x₁ y₁ z₁ := by
  by_cases hsamePos : x₁ = x₂ ∧ y₁ = y₂ ∧ z₁ = z₂
  · rcases hsamePos with ⟨rfl, rfl, rfl⟩
    rfl
  · have wf₁ : WellFormed n (toggleLight n config x₁ y₁ z₁) :=
      toggleLight_preserves_WellFormed n config wf x₁ y₁ z₁ hx₁ hy₁ hz₁
    have wf₂ : WellFormed n (toggleLight n config x₂ y₂ z₂) :=
      toggleLight_preserves_WellFormed n config wf x₂ y₂ z₂ hx₂ hy₂ hz₂
    have wfL : WellFormed n (toggleLight n (toggleLight n config x₁ y₁ z₁) x₂ y₂ z₂) :=
      toggleLight_preserves_WellFormed n (toggleLight n config x₁ y₁ z₁) wf₁ x₂ y₂ z₂ hx₂ hy₂ hz₂
    have wfR : WellFormed n (toggleLight n (toggleLight n config x₂ y₂ z₂) x₁ y₁ z₁) :=
      toggleLight_preserves_WellFormed n (toggleLight n config x₂ y₂ z₂) wf₂ x₁ y₁ z₁ hx₁ hy₁ hz₁
    apply config_ext n _ _ wfL wfR
    intro x y z hx hy hz
    by_cases hq₁ : x = x₁ ∧ y = y₁ ∧ z = z₁
    · have hq₂ : ¬(x₂ = x ∧ y₂ = y ∧ z₂ = z) := by
        intro h
        apply hsamePos
        rcases hq₁ with ⟨hxQ, hyQ, hzQ⟩
        exact ⟨(h.1.trans hxQ).symm, (h.2.1.trans hyQ).symm, (h.2.2.trans hzQ).symm⟩
      rcases hq₁ with ⟨hxQ, hyQ, hzQ⟩
      subst x
      subst y
      subst z
      rw [getLight_toggleLight_same n (toggleLight n config x₂ y₂ z₂) x₁ y₁ z₁ wf₂ hx₁ hy₁ hz₁]
      rw [getLight_toggleLight_diff n config x₂ y₂ z₂ x₁ y₁ z₁ wf hq₂]
      rw [getLight_toggleLight_diff n (toggleLight n config x₁ y₁ z₁) x₂ y₂ z₂ x₁ y₁ z₁ wf₁ hq₂]
      rw [getLight_toggleLight_same n config x₁ y₁ z₁ wf hx₁ hy₁ hz₁]
    · by_cases hq₂ : x = x₂ ∧ y = y₂ ∧ z = z₂
      · have hq₁' : ¬(x₁ = x ∧ y₁ = y ∧ z₁ = z) := by
          intro h
          apply hsamePos
          rcases hq₂ with ⟨hxQ, hyQ, hzQ⟩
          exact ⟨h.1.trans hxQ, h.2.1.trans hyQ, h.2.2.trans hzQ⟩
        rcases hq₂ with ⟨hxQ, hyQ, hzQ⟩
        subst x
        subst y
        subst z
        rw [getLight_toggleLight_same n (toggleLight n config x₁ y₁ z₁) x₂ y₂ z₂ wf₁ hx₂ hy₂ hz₂]
        rw [getLight_toggleLight_diff n config x₁ y₁ z₁ x₂ y₂ z₂ wf hq₁']
        rw [getLight_toggleLight_diff n (toggleLight n config x₂ y₂ z₂) x₁ y₁ z₁ x₂ y₂ z₂ wf₂ hq₁']
        rw [getLight_toggleLight_same n config x₂ y₂ z₂ wf hx₂ hy₂ hz₂]
      · have hq₁' : ¬(x₁ = x ∧ y₁ = y ∧ z₁ = z) := by
          intro h
          exact hq₁ ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
        have hq₂' : ¬(x₂ = x ∧ y₂ = y ∧ z₂ = z) := by
          intro h
          exact hq₂ ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
        rw [getLight_toggleLight_diff n (toggleLight n config x₁ y₁ z₁) x₂ y₂ z₂ x y z wf₁ hq₂']
        rw [getLight_toggleLight_diff n config x₁ y₁ z₁ x y z wf hq₁']
        rw [getLight_toggleLight_diff n (toggleLight n config x₂ y₂ z₂) x₁ y₁ z₁ x y z wf₂ hq₁']
        rw [getLight_toggleLight_diff n config x₂ y₂ z₂ x y z wf hq₂']

theorem toggleLight_eq_self_of_not_in_bounds (n : Nat) (config : Config n) (x y z : Nat)
    (h : ¬(x < n ∧ y < n ∧ z < n)) :
    toggleLight n config x y z = config := by
  simp [toggleLight, setLight, h]

theorem toggleLight_preserves_WellFormed_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z : Nat) :
    WellFormed n (toggleLight n config x y z) := by
  by_cases h : x < n ∧ y < n ∧ z < n
  · exact toggleLight_preserves_WellFormed n config wf x y z h.1 h.2.1 h.2.2
  · rw [toggleLight_eq_self_of_not_in_bounds n config x y z h]
    exact wf

theorem toggleLight_involutive_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z : Nat) :
    toggleLight n (toggleLight n config x y z) x y z = config := by
  by_cases h : x < n ∧ y < n ∧ z < n
  · exact toggleLight_involutive n config wf x y z h.1 h.2.1 h.2.2
  · rw [toggleLight_eq_self_of_not_in_bounds n config x y z h]
    rw [toggleLight_eq_self_of_not_in_bounds n config x y z h]

theorem toggleLight_comm_any (n : Nat) (config : Config n)
    (x₁ y₁ z₁ x₂ y₂ z₂ : Nat) (wf : WellFormed n config) :
    toggleLight n (toggleLight n config x₁ y₁ z₁) x₂ y₂ z₂ =
    toggleLight n (toggleLight n config x₂ y₂ z₂) x₁ y₁ z₁ := by
  by_cases h₁ : x₁ < n ∧ y₁ < n ∧ z₁ < n
  · by_cases h₂ : x₂ < n ∧ y₂ < n ∧ z₂ < n
    · exact toggleLight_comm n config x₁ y₁ z₁ x₂ y₂ z₂ wf h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
    · rw [toggleLight_eq_self_of_not_in_bounds n (toggleLight n config x₁ y₁ z₁) x₂ y₂ z₂ h₂]
      rw [toggleLight_eq_self_of_not_in_bounds n config x₂ y₂ z₂ h₂]
  · by_cases h₂ : x₂ < n ∧ y₂ < n ∧ z₂ < n
    · rw [toggleLight_eq_self_of_not_in_bounds n (toggleLight n config x₂ y₂ z₂) x₁ y₁ z₁ h₁]
      rw [toggleLight_eq_self_of_not_in_bounds n config x₁ y₁ z₁ h₁]
    · rw [toggleLight_eq_self_of_not_in_bounds n (toggleLight n config x₁ y₁ z₁) x₂ y₂ z₂ h₂]
      rw [toggleLight_eq_self_of_not_in_bounds n (toggleLight n config x₂ y₂ z₂) x₁ y₁ z₁ h₁]
      rw [toggleLight_eq_self_of_not_in_bounds n config x₁ y₁ z₁ h₁]
      rw [toggleLight_eq_self_of_not_in_bounds n config x₂ y₂ z₂ h₂]

theorem toggleAt_preserves_WellFormed_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (coord : Coord) :
    WellFormed n (toggleAt n config coord) := by
  exact toggleLight_preserves_WellFormed_any n config wf coord.1 coord.2.1 coord.2.2

theorem toggleAt_comm_any (n : Nat) (config : Config n)
    (coord₁ coord₂ : Coord) (wf : WellFormed n config) :
    toggleAt n (toggleAt n config coord₁) coord₂ =
    toggleAt n (toggleAt n config coord₂) coord₁ := by
  exact toggleLight_comm_any n config coord₁.1 coord₁.2.1 coord₁.2.2 coord₂.1 coord₂.2.1 coord₂.2.2 wf

theorem foldl_commute_right {α : Type} {β : Type}
    (f : α → β → α)
    (hcomm : ∀ a b c, f (f a b) c = f (f a c) b) :
    ∀ l a b, List.foldl f (f a b) l = f (List.foldl f a l) b := by
  intro l
  induction l with
  | nil =>
      intro a b
      rfl
  | cons c l ih =>
      intro a b
      calc
        List.foldl f (f a b) (c :: l)
          = List.foldl f (f (f a b) c) l := rfl
        _ = List.foldl f (f (f a c) b) l := by rw [hcomm a b c]
        _ = f (List.foldl f (f a c) l) b := ih _ _
        _ = f (List.foldl f a (c :: l)) b := rfl

theorem foldl_cancel_of_involutive_comm {α : Type} {β : Type}
    (f : α → β → α)
    (hcomm : ∀ a b c, f (f a b) c = f (f a c) b)
    (hinv : ∀ a b, f (f a b) b = a) :
    ∀ l a, List.foldl f (List.foldl f a l) l = a := by
  intro l
  induction l with
  | nil =>
      intro a
      rfl
  | cons b l ih =>
      intro a
      calc
        List.foldl f (List.foldl f a (b :: l)) (b :: l)
          = List.foldl f (List.foldl f (f a b) l) (b :: l) := rfl
        _ = f (List.foldl f (List.foldl f (f a b) l) l) b := by
          let x := List.foldl f (f a b) l
          calc
            List.foldl f x (b :: l) = List.foldl f (f x b) l := rfl
            _ = f (List.foldl f x l) b := foldl_commute_right f hcomm l x b
        _ = f (f a b) b := by rw [ih (f a b)]
        _ = a := hinv a b

theorem foldl_comm_of_pairwise {α : Type} {β : Type} {γ : Type}
    (f : α → β → α) (g : α → γ → α)
    (hcomm : ∀ a b c, g (f a b) c = f (g a c) b) :
    ∀ l₁ l₂ a, List.foldl g (List.foldl f a l₁) l₂ = List.foldl f (List.foldl g a l₂) l₁ := by
  have hright : ∀ l a c, List.foldl f (g a c) l = g (List.foldl f a l) c := by
    intro l
    induction l with
    | nil =>
        intro a c
        rfl
    | cons b l ih =>
        intro a c
        calc
          List.foldl f (g a c) (b :: l)
            = List.foldl f (f (g a c) b) l := rfl
          _ = List.foldl f (g (f a b) c) l := by rw [(hcomm a b c).symm]
          _ = g (List.foldl f (f a b) l) c := ih _ _
          _ = g (List.foldl f a (b :: l)) c := rfl
  intro l₁ l₂
  induction l₂ with
  | nil =>
      intro a
      simp
  | cons c l ih =>
      intro a
      calc
        List.foldl g (List.foldl f a l₁) (c :: l)
          = List.foldl g (g (List.foldl f a l₁) c) l := rfl
        _ = List.foldl g (List.foldl f (g a c) l₁) l := by
          rw [(hright l₁ a c).symm]
        _ = List.foldl f (List.foldl g (g a c) l) l₁ := ih _
        _ = List.foldl f (List.foldl g a (c :: l)) l₁ := rfl

theorem foldl_preserves_WellFormed {α : Type} (n : Nat) (l : List α)
    (step : Config n → α → Config n)
    (hstep : ∀ cfg a, WellFormed n cfg → WellFormed n (step cfg a))
    (config : Config n) (wf : WellFormed n config) :
    WellFormed n (List.foldl step config l) := by
  induction l generalizing config with
  | nil => simpa using wf
  | cons a l ih =>
      simp
      apply ih
      exact hstep config a wf

theorem applyMove_preserves_WellFormed (n : Nat) (m : Move n) (config : Config n)
    (wf : WellFormed n config) :
    WellFormed n (applyMove n m config) := by
  cases m with
  | mk dir u v =>
    cases dir <;> simp [applyMove]
    · refine foldl_preserves_WellFormed n (List.range n) (fun cfg i => toggleLight n cfg i u v) ?_ config wf
      intro cfg i hcfg
      exact toggleLight_preserves_WellFormed_any n cfg hcfg i u v
    · refine foldl_preserves_WellFormed n (List.range n) (fun cfg j => toggleLight n cfg u j v) ?_ config wf
      intro cfg j hcfg
      exact toggleLight_preserves_WellFormed_any n cfg hcfg u j v
    · refine foldl_preserves_WellFormed n (List.range n) (fun cfg k => toggleLight n cfg u v k) ?_ config wf
      intro cfg k hcfg
      exact toggleLight_preserves_WellFormed_any n cfg hcfg u v k

theorem applyMoves_preserves_WellFormed (n : Nat) (moves : List (Move n)) (config : Config n)
    (wf : WellFormed n config) :
    WellFormed n (applyMoves n moves config) := by
  unfold applyMoves
  refine foldl_preserves_WellFormed n moves (fun cfg m => applyMove n m cfg) ?_ config wf
  intro cfg m hcfg
  exact applyMove_preserves_WellFormed n m cfg hcfg

theorem processSurface_preserves_WellFormed (n : Nat) (dir : Direction) (config : Config n)
    (wf : WellFormed n config) :
    WellFormed n (processSurface n dir config) := by
  unfold processSurface
  refine foldl_preserves_WellFormed n (List.range n)
    (fun cfg₁ u =>
      (List.range n).foldl (fun cfg₂ v =>
        let lit := match dir with
          | Direction.x => getLight n cfg₂ 0 u v
          | Direction.y => getLight n cfg₂ u 0 v
          | Direction.z => getLight n cfg₂ u v 0
        if lit = 1 then
          applyMove n ⟨dir, u, v⟩ cfg₂
        else cfg₂) cfg₁) ?_ config wf
  intro cfg₁ u hcfg₁
  refine foldl_preserves_WellFormed n (List.range n)
    (fun cfg₂ v =>
      let lit := match dir with
        | Direction.x => getLight n cfg₂ 0 u v
        | Direction.y => getLight n cfg₂ u 0 v
        | Direction.z => getLight n cfg₂ u v 0
      if lit = 1 then
        applyMove n ⟨dir, u, v⟩ cfg₂
      else cfg₂) ?_ cfg₁ hcfg₁
  intro cfg₂ v hcfg₂
  by_cases hlit : (match dir with
      | Direction.x => getLight n cfg₂ 0 u v
      | Direction.y => getLight n cfg₂ u 0 v
      | Direction.z => getLight n cfg₂ u v 0) = 1
  · simp [hlit]
    exact applyMove_preserves_WellFormed n ⟨dir, u, v⟩ cfg₂ hcfg₂
  · simp [hlit]
    exact hcfg₂

theorem processXSurface_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) :
    WellFormed n (processXSurface n config) := by
  simpa [processXSurface] using processSurface_preserves_WellFormed n Direction.x config wf

theorem processYSurface_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) :
    WellFormed n (processYSurface n config) := by
  simpa [processYSurface] using processSurface_preserves_WellFormed n Direction.y config wf

theorem processZSurface_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) :
    WellFormed n (processZSurface n config) := by
  simpa [processZSurface] using processSurface_preserves_WellFormed n Direction.z config wf

theorem greedyAlgorithm_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) :
    WellFormed n (greedyAlgorithm n config) := by
  unfold greedyAlgorithm
  exact processZSurface_preserves_WellFormed n _
    (processYSurface_preserves_WellFormed n _
      (processXSurface_preserves_WellFormed n config wf))

theorem foldl_toggle_family_comm (n : Nat) (config : Config n)
    (wf : WellFormed n config) (fam₁ fam₂ : Nat → Coord) (l₁ l₂ : List Nat) :
    List.foldl (fun cfg j => toggleAt n cfg (fam₂ j))
      (List.foldl (fun cfg i => toggleAt n cfg (fam₁ i)) config l₁) l₂ =
    List.foldl (fun cfg i => toggleAt n cfg (fam₁ i))
      (List.foldl (fun cfg j => toggleAt n cfg (fam₂ j)) config l₂) l₁ := by
  let step₁ : {cfg : Config n // WellFormed n cfg} → Nat → {cfg : Config n // WellFormed n cfg} :=
    fun cfg i => ⟨toggleAt n cfg.1 (fam₁ i), toggleAt_preserves_WellFormed_any n cfg.1 cfg.2 (fam₁ i)⟩
  let step₂ : {cfg : Config n // WellFormed n cfg} → Nat → {cfg : Config n // WellFormed n cfg} :=
    fun cfg j => ⟨toggleAt n cfg.1 (fam₂ j), toggleAt_preserves_WellFormed_any n cfg.1 cfg.2 (fam₂ j)⟩
  have hcomm : ∀ a i j, step₂ (step₁ a i) j = step₁ (step₂ a j) i := by
    intro a i j
    apply Subtype.ext
    simp [step₁, step₂, toggleAt]
    exact toggleAt_comm_any n a.1 (fam₁ i) (fam₂ j) a.2
  have hfold := foldl_comm_of_pairwise step₁ step₂ hcomm l₁ l₂ ⟨config, wf⟩
  have hval₁ : ∀ l s, (List.foldl step₁ s l).1 = List.foldl (fun cfg i => toggleAt n cfg (fam₁ i)) s.1 l := by
    intro l s
    induction l generalizing s with
    | nil => rfl
    | cons b l ih => simp [step₁, ih]
  have hval₂ : ∀ l s, (List.foldl step₂ s l).1 = List.foldl (fun cfg j => toggleAt n cfg (fam₂ j)) s.1 l := by
    intro l s
    induction l generalizing s with
    | nil => rfl
    | cons b l ih => simp [step₂, ih]
  have hfold' := congrArg Subtype.val hfold
  rw [hval₂ l₂ (List.foldl step₁ ⟨config, wf⟩ l₁)] at hfold'
  rw [hval₁ l₁ ⟨config, wf⟩] at hfold'
  rw [hval₁ l₁ (List.foldl step₂ ⟨config, wf⟩ l₂)] at hfold'
  rw [hval₂ l₂ ⟨config, wf⟩] at hfold'
  simpa using hfold'

namespace ValidConfig

instance {n : Nat} : Coe (ValidConfig n) (Config n) where
  coe := ValidConfig.data

def ofConfig {n : Nat} (config : Config n) (wf : WellFormed n config) : ValidConfig n :=
  ⟨config, wf⟩

def toggleLight {n : Nat} (config : ValidConfig n) (x y z : Nat) : ValidConfig n :=
  ⟨LightPuzzle.toggleLight n config.data x y z,
    toggleLight_preserves_WellFormed_any n config.data config.wf x y z⟩

def applyMove {n : Nat} (config : ValidConfig n) (move : Move n) : ValidConfig n :=
  ⟨LightPuzzle.applyMove n move config.data,
    applyMove_preserves_WellFormed n move config.data config.wf⟩

def applyMoves {n : Nat} (config : ValidConfig n) (moves : List (Move n)) : ValidConfig n :=
  ⟨LightPuzzle.applyMoves n moves config.data,
    applyMoves_preserves_WellFormed n moves config.data config.wf⟩

def processSurface {n : Nat} (dir : Direction) (config : ValidConfig n) : ValidConfig n :=
  ⟨LightPuzzle.processSurface n dir config.data,
    processSurface_preserves_WellFormed n dir config.data config.wf⟩

def processXSurface {n : Nat} (config : ValidConfig n) : ValidConfig n :=
  ⟨LightPuzzle.processXSurface n config.data,
    processXSurface_preserves_WellFormed n config.data config.wf⟩

def processYSurface {n : Nat} (config : ValidConfig n) : ValidConfig n :=
  ⟨LightPuzzle.processYSurface n config.data,
    processYSurface_preserves_WellFormed n config.data config.wf⟩

def processZSurface {n : Nat} (config : ValidConfig n) : ValidConfig n :=
  ⟨LightPuzzle.processZSurface n config.data,
    processZSurface_preserves_WellFormed n config.data config.wf⟩

def greedyAlgorithm {n : Nat} (config : ValidConfig n) : ValidConfig n :=
  ⟨LightPuzzle.greedyAlgorithm n config.data,
    greedyAlgorithm_preserves_WellFormed n config.data config.wf⟩

def isAllOff {n : Nat} (config : ValidConfig n) : Bool :=
  LightPuzzle.isAllOff n config.data

def IsAllOff {n : Nat} (config : ValidConfig n) : Prop :=
  LightPuzzle.IsAllOff n config.data

theorem ext {n : Nat} (config₁ config₂ : ValidConfig n)
    (h : ∀ x y z, x < n → y < n → z < n →
      getLight n config₁.data x y z = getLight n config₂.data x y z) :
    config₁ = config₂ := by
  cases config₁ with
  | mk data₁ wf₁ =>
    cases config₂ with
    | mk data₂ wf₂ =>
      have hdata : data₁ = data₂ := config_ext n data₁ data₂ wf₁ wf₂ h
      subst hdata
      simp

end ValidConfig

/-! ## Lemmas and Theorems -/

-- Progress note (GPT-5.4, 2026-04-07):
-- The next natural targets are `applyMove_cancel` and `applyMove_comm`.
-- Looking back at the actual puzzle statement, these should be proved in the binary
-- `WellFormed` setting. The raw statements over arbitrary nested `Nat` lists are too
-- strong, because malformed shapes and values > 1 create counterexamples.

-- A move applied twice cancels itself (toggle is an involution)
theorem applyMove_cancel (n : Nat) (m : Move n) (config : Config n)
    (wf : WellFormed n config) :
    applyMove n m (applyMove n m config) = config := by
  cases m with
  | mk dir u v =>
    cases dir with
  | x =>
      simp [applyMove]
      let step : {cfg : Config n // WellFormed n cfg} → Nat → {cfg : Config n // WellFormed n cfg} :=
        fun cfg i => ⟨toggleLight n cfg.1 i u v, toggleLight_preserves_WellFormed_any n cfg.1 cfg.2 i u v⟩
      have hcomm : ∀ a i j, step (step a i) j = step (step a j) i := by
        intro a i j
        apply Subtype.ext
        simp [step]
        exact toggleLight_comm_any n a.1 i u v j u v a.2
      have hinv : ∀ a i, step (step a i) i = a := by
        intro a i
        apply Subtype.ext
        simp [step]
        exact toggleLight_involutive_any n a.1 a.2 i u v
      have hfold := foldl_cancel_of_involutive_comm step hcomm hinv (List.range n) ⟨config, wf⟩
      have hval : ∀ l s, (List.foldl step s l).1 = List.foldl (fun cfg i => toggleLight n cfg i u v) s.1 l := by
        intro l s
        induction l generalizing s with
        | nil => rfl
        | cons b l ih => simp [step, ih]
      have hfold' := congrArg Subtype.val hfold
      rw [hval (List.range n) (List.foldl step ⟨config, wf⟩ (List.range n))] at hfold'
      rw [hval (List.range n) ⟨config, wf⟩] at hfold'
      simpa using hfold'
  | y =>
      simp [applyMove]
      let step : {cfg : Config n // WellFormed n cfg} → Nat → {cfg : Config n // WellFormed n cfg} :=
        fun cfg j => ⟨toggleLight n cfg.1 u j v, toggleLight_preserves_WellFormed_any n cfg.1 cfg.2 u j v⟩
      have hcomm : ∀ a i j, step (step a i) j = step (step a j) i := by
        intro a i j
        apply Subtype.ext
        simp [step]
        exact toggleLight_comm_any n a.1 u i v u j v a.2
      have hinv : ∀ a i, step (step a i) i = a := by
        intro a i
        apply Subtype.ext
        simp [step]
        exact toggleLight_involutive_any n a.1 a.2 u i v
      have hfold := foldl_cancel_of_involutive_comm step hcomm hinv (List.range n) ⟨config, wf⟩
      have hval : ∀ l s, (List.foldl step s l).1 = List.foldl (fun cfg j => toggleLight n cfg u j v) s.1 l := by
        intro l s
        induction l generalizing s with
        | nil => rfl
        | cons b l ih => simp [step, ih]
      have hfold' := congrArg Subtype.val hfold
      rw [hval (List.range n) (List.foldl step ⟨config, wf⟩ (List.range n))] at hfold'
      rw [hval (List.range n) ⟨config, wf⟩] at hfold'
      simpa using hfold'
  | z =>
      simp [applyMove]
      let step : {cfg : Config n // WellFormed n cfg} → Nat → {cfg : Config n // WellFormed n cfg} :=
        fun cfg k => ⟨toggleLight n cfg.1 u v k, toggleLight_preserves_WellFormed_any n cfg.1 cfg.2 u v k⟩
      have hcomm : ∀ a i j, step (step a i) j = step (step a j) i := by
        intro a i j
        apply Subtype.ext
        simp [step]
        exact toggleLight_comm_any n a.1 u v i u v j a.2
      have hinv : ∀ a i, step (step a i) i = a := by
        intro a i
        apply Subtype.ext
        simp [step]
        exact toggleLight_involutive_any n a.1 a.2 u v i
      have hfold := foldl_cancel_of_involutive_comm step hcomm hinv (List.range n) ⟨config, wf⟩
      have hval : ∀ l s, (List.foldl step s l).1 = List.foldl (fun cfg k => toggleLight n cfg u v k) s.1 l := by
        intro l s
        induction l generalizing s with
        | nil => rfl
        | cons b l ih => simp [step, ih]
      have hfold' := congrArg Subtype.val hfold
      rw [hval (List.range n) (List.foldl step ⟨config, wf⟩ (List.range n))] at hfold'
      rw [hval (List.range n) ⟨config, wf⟩] at hfold'
      simpa using hfold'

theorem applyMove_preserves_IsSolvable (n : Nat) (config : Config n)
    (wf : WellFormed n config) (m : Move n) :
    IsSolvable n config ↔ IsSolvable n (applyMove n m config) := by
  constructor
  · intro hsolv
    rcases hsolv with ⟨moves, hOff⟩
    refine ⟨m :: moves, ?_⟩
    simp [applyMoves]
    rw [applyMove_cancel n m config wf]
    exact hOff
  · intro hsolv
    rcases hsolv with ⟨moves, hOff⟩
    refine ⟨m :: moves, ?_⟩
    simp [applyMoves]
    exact hOff

theorem applyMoves_preserves_IsSolvable (n : Nat) (config : Config n)
    (wf : WellFormed n config) (moves : List (Move n)) :
    IsSolvable n config ↔ IsSolvable n (applyMoves n moves config) := by
  induction moves generalizing config wf with
  | nil =>
      simp [applyMoves]
  | cons move moves ih =>
      simp [applyMoves]
      have hmove := applyMove_preserves_IsSolvable n config wf move
      have wf' : WellFormed n (applyMove n move config) :=
        applyMove_preserves_WellFormed n move config wf
      exact hmove.trans (ih (applyMove n move config) wf')

theorem greedyAlgorithm_preserves_IsSolvable (n : Nat) (config : Config n)
    (wf : WellFormed n config) :
    IsSolvable n config ↔ IsSolvable n (greedyAlgorithm n config) := by
  rw [← greedyAlgorithmTrace_fst n config, ← greedyAlgorithmTrace_sound n config]
  simpa using applyMoves_preserves_IsSolvable n config wf (greedyAlgorithmTrace n config).2

-- Two moves commute on legal puzzle states.
theorem applyMove_comm (n : Nat) (m1 m2 : Move n) (config : Config n)
  (wf : WellFormed n config) :
  applyMove n m1 (applyMove n m2 config) = applyMove n m2 (applyMove n m1 config) := by
  cases m1 with
  | mk dir₁ u₁ v₁ =>
    cases m2 with
    | mk dir₂ u₂ v₂ =>
      cases dir₁ with
      | x =>
          cases dir₂ with
          | x =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (i, u₂, v₂)) (fun j => (j, u₁, v₁)) (List.range n) (List.range n)
          | y =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (u₂, i, v₂)) (fun j => (j, u₁, v₁)) (List.range n) (List.range n)
          | z =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (u₂, v₂, i)) (fun j => (j, u₁, v₁)) (List.range n) (List.range n)
      | y =>
          cases dir₂ with
          | x =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (i, u₂, v₂)) (fun j => (u₁, j, v₁)) (List.range n) (List.range n)
          | y =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (u₂, i, v₂)) (fun j => (u₁, j, v₁)) (List.range n) (List.range n)
          | z =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (u₂, v₂, i)) (fun j => (u₁, j, v₁)) (List.range n) (List.range n)
      | z =>
          cases dir₂ with
          | x =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (i, u₂, v₂)) (fun j => (u₁, v₁, j)) (List.range n) (List.range n)
          | y =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (u₂, i, v₂)) (fun j => (u₁, v₁, j)) (List.range n) (List.range n)
          | z =>
              simpa [applyMove, toggleAt] using foldl_toggle_family_comm n config wf
                (fun i => (u₂, v₂, i)) (fun j => (u₁, v₁, j)) (List.range n) (List.range n)

theorem foldl_toggleX_tail_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (uLine vLine uTarget vTarget : Nat) :
    getLight n (List.foldl (fun cfg i => toggleLight n cfg i uLine vLine) config (l.map Nat.succ))
      0 uTarget vTarget =
    getLight n config 0 uTarget vTarget := by
  induction l generalizing config with
  | nil =>
      rfl
  | cons i l ih =>
      simp only [List.map, List.foldl_cons]
      have hwf' : WellFormed n (toggleLight n config (Nat.succ i) uLine vLine) :=
        toggleLight_preserves_WellFormed_any n config wf (Nat.succ i) uLine vLine
      have hstep :
          getLight n (toggleLight n config (Nat.succ i) uLine vLine) 0 uTarget vTarget =
            getLight n config 0 uTarget vTarget := by
        apply getLight_toggleLight_diff n config (Nat.succ i) uLine vLine 0 uTarget vTarget wf
        intro h
        rcases h with ⟨hx, _, _⟩
        omega
      rw [ih _ hwf', hstep]

theorem foldl_toggleY_tail_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (uLine vLine uTarget vTarget : Nat) :
    getLight n (List.foldl (fun cfg j => toggleLight n cfg uLine j vLine) config (l.map Nat.succ))
      uTarget 0 vTarget =
    getLight n config uTarget 0 vTarget := by
  induction l generalizing config with
  | nil =>
      rfl
  | cons j l ih =>
      simp only [List.map, List.foldl_cons]
      have hwf' : WellFormed n (toggleLight n config uLine (Nat.succ j) vLine) :=
        toggleLight_preserves_WellFormed_any n config wf uLine (Nat.succ j) vLine
      have hstep :
          getLight n (toggleLight n config uLine (Nat.succ j) vLine) uTarget 0 vTarget =
            getLight n config uTarget 0 vTarget := by
        apply getLight_toggleLight_diff n config uLine (Nat.succ j) vLine uTarget 0 vTarget wf
        intro h
        rcases h with ⟨_, hy, _⟩
        omega
      rw [ih _ hwf', hstep]

theorem foldl_toggleZ_tail_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (uLine vLine uTarget vTarget : Nat) :
    getLight n (List.foldl (fun cfg k => toggleLight n cfg uLine vLine k) config (l.map Nat.succ))
      uTarget vTarget 0 =
    getLight n config uTarget vTarget 0 := by
  induction l generalizing config with
  | nil =>
      rfl
  | cons k l ih =>
      simp only [List.map, List.foldl_cons]
      have hwf' : WellFormed n (toggleLight n config uLine vLine (Nat.succ k)) :=
        toggleLight_preserves_WellFormed_any n config wf uLine vLine (Nat.succ k)
      have hstep :
          getLight n (toggleLight n config uLine vLine (Nat.succ k)) uTarget vTarget 0 =
            getLight n config uTarget vTarget 0 := by
        apply getLight_toggleLight_diff n config uLine vLine (Nat.succ k) uTarget vTarget 0 wf
        intro h
        rcases h with ⟨_, _, hz⟩
        omega
      rw [ih _ hwf', hstep]

theorem getLight_applyMoveX_same (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v : Nat) (hu : u < n) (hv : v < n) :
    getLight n (applyMove n ⟨Direction.x, u, v⟩ config) 0 u v = ((getLight n config 0 u v) + 1) % 2 := by
  cases n with
  | zero =>
      cases hu
  | succ n' =>
      rw [applyMove, List.range_succ_eq_map]
      simp only [List.foldl_cons]
      have h0 : 0 < Nat.succ n' := by simp
      have hwf' : WellFormed (Nat.succ n') (toggleLight (Nat.succ n') config 0 u v) :=
        toggleLight_preserves_WellFormed (Nat.succ n') config wf 0 u v h0 hu hv
      rw [foldl_toggleX_tail_preserves_front (n := Nat.succ n')
        (config := toggleLight (Nat.succ n') config 0 u v) (wf := hwf')
        (l := List.range n') (uLine := u) (vLine := v) (uTarget := u) (vTarget := v)]
      exact getLight_toggleLight_same (Nat.succ n') config 0 u v wf h0 hu hv

theorem getLight_applyMoveY_same (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v : Nat) (hu : u < n) (hv : v < n) :
    getLight n (applyMove n ⟨Direction.y, u, v⟩ config) u 0 v = ((getLight n config u 0 v) + 1) % 2 := by
  cases n with
  | zero =>
      cases hu
  | succ n' =>
      rw [applyMove, List.range_succ_eq_map]
      simp only [List.foldl_cons]
      have h0 : 0 < Nat.succ n' := by simp
      have hwf' : WellFormed (Nat.succ n') (toggleLight (Nat.succ n') config u 0 v) :=
        toggleLight_preserves_WellFormed (Nat.succ n') config wf u 0 v hu h0 hv
      rw [foldl_toggleY_tail_preserves_front (n := Nat.succ n')
        (config := toggleLight (Nat.succ n') config u 0 v) (wf := hwf')
        (l := List.range n') (uLine := u) (vLine := v) (uTarget := u) (vTarget := v)]
      exact getLight_toggleLight_same (Nat.succ n') config u 0 v wf hu h0 hv

theorem getLight_applyMoveZ_same (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v : Nat) (hu : u < n) (hv : v < n) :
    getLight n (applyMove n ⟨Direction.z, u, v⟩ config) u v 0 = ((getLight n config u v 0) + 1) % 2 := by
  cases n with
  | zero =>
      cases hu
  | succ n' =>
      rw [applyMove, List.range_succ_eq_map]
      simp only [List.foldl_cons]
      have h0 : 0 < Nat.succ n' := by simp
      have hwf' : WellFormed (Nat.succ n') (toggleLight (Nat.succ n') config u v 0) :=
        toggleLight_preserves_WellFormed (Nat.succ n') config wf u v 0 hu hv h0
      rw [foldl_toggleZ_tail_preserves_front (n := Nat.succ n')
        (config := toggleLight (Nat.succ n') config u v 0) (wf := hwf')
        (l := List.range n') (uLine := u) (vLine := v) (uTarget := u) (vTarget := v)]
      exact getLight_toggleLight_same (Nat.succ n') config u v 0 wf hu hv h0

theorem getLight_applyMoveX_diff (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine vLine uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n)
    (hne : uLine ≠ uTarget ∨ vLine ≠ vTarget) :
    getLight n (applyMove n ⟨Direction.x, uLine, vLine⟩ config) 0 uTarget vTarget =
      getLight n config 0 uTarget vTarget := by
  cases n with
  | zero =>
      cases hu
  | succ n' =>
      rw [applyMove, List.range_succ_eq_map]
      simp only [List.foldl_cons]
      have hstep :
          getLight (Nat.succ n') (toggleLight (Nat.succ n') config 0 uLine vLine) 0 uTarget vTarget =
            getLight (Nat.succ n') config 0 uTarget vTarget := by
        apply getLight_toggleLight_diff (Nat.succ n') config 0 uLine vLine 0 uTarget vTarget wf
        intro h
        rcases h with ⟨_, hy, hz⟩
        cases hne with
        | inl hneq => exact hneq hy
        | inr hneq => exact hneq hz
      have hwf' : WellFormed (Nat.succ n') (toggleLight (Nat.succ n') config 0 uLine vLine) :=
        toggleLight_preserves_WellFormed_any (Nat.succ n') config wf 0 uLine vLine
      rw [foldl_toggleX_tail_preserves_front (n := Nat.succ n')
        (config := toggleLight (Nat.succ n') config 0 uLine vLine) (wf := hwf')
        (l := List.range n') (uLine := uLine) (vLine := vLine) (uTarget := uTarget) (vTarget := vTarget)]
      exact hstep

theorem getLight_applyMoveY_diff (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine vLine uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n)
    (hne : uLine ≠ uTarget ∨ vLine ≠ vTarget) :
    getLight n (applyMove n ⟨Direction.y, uLine, vLine⟩ config) uTarget 0 vTarget =
      getLight n config uTarget 0 vTarget := by
  cases n with
  | zero =>
      cases hu
  | succ n' =>
      rw [applyMove, List.range_succ_eq_map]
      simp only [List.foldl_cons]
      have hstep :
          getLight (Nat.succ n') (toggleLight (Nat.succ n') config uLine 0 vLine) uTarget 0 vTarget =
            getLight (Nat.succ n') config uTarget 0 vTarget := by
        apply getLight_toggleLight_diff (Nat.succ n') config uLine 0 vLine uTarget 0 vTarget wf
        intro h
        rcases h with ⟨hx, _, hz⟩
        cases hne with
        | inl hneq => exact hneq hx
        | inr hneq => exact hneq hz
      have hwf' : WellFormed (Nat.succ n') (toggleLight (Nat.succ n') config uLine 0 vLine) :=
        toggleLight_preserves_WellFormed_any (Nat.succ n') config wf uLine 0 vLine
      rw [foldl_toggleY_tail_preserves_front (n := Nat.succ n')
        (config := toggleLight (Nat.succ n') config uLine 0 vLine) (wf := hwf')
        (l := List.range n') (uLine := uLine) (vLine := vLine) (uTarget := uTarget) (vTarget := vTarget)]
      exact hstep

theorem getLight_applyMoveZ_diff (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine vLine uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n)
    (hne : uLine ≠ uTarget ∨ vLine ≠ vTarget) :
    getLight n (applyMove n ⟨Direction.z, uLine, vLine⟩ config) uTarget vTarget 0 =
      getLight n config uTarget vTarget 0 := by
  cases n with
  | zero =>
      cases hu
  | succ n' =>
      rw [applyMove, List.range_succ_eq_map]
      simp only [List.foldl_cons]
      have hstep :
          getLight (Nat.succ n') (toggleLight (Nat.succ n') config uLine vLine 0) uTarget vTarget 0 =
            getLight (Nat.succ n') config uTarget vTarget 0 := by
        apply getLight_toggleLight_diff (Nat.succ n') config uLine vLine 0 uTarget vTarget 0 wf
        intro h
        rcases h with ⟨hx, hy, _⟩
        cases hne with
        | inl hneq => exact hneq hx
        | inr hneq => exact hneq hy
      have hwf' : WellFormed (Nat.succ n') (toggleLight (Nat.succ n') config uLine vLine 0) :=
        toggleLight_preserves_WellFormed_any (Nat.succ n') config wf uLine vLine 0
      rw [foldl_toggleZ_tail_preserves_front (n := Nat.succ n')
        (config := toggleLight (Nat.succ n') config uLine vLine 0) (wf := hwf')
        (l := List.range n') (uLine := uLine) (vLine := vLine) (uTarget := uTarget) (vTarget := vTarget)]
      exact hstep

theorem foldl_toggleX_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (xTarget yLine zLine yTarget zTarget : Nat)
    (hne : yLine ≠ yTarget ∨ zLine ≠ zTarget) :
    getLight n (l.foldl (fun cfg xLine => toggleLight n cfg xLine yLine zLine) config) xTarget yTarget zTarget =
      getLight n config xTarget yTarget zTarget := by
  induction l generalizing config wf with
  | nil =>
      rfl
  | cons xLine l ih =>
      simp only [List.foldl_cons]
      have hstep :
          getLight n (toggleLight n config xLine yLine zLine) xTarget yTarget zTarget =
            getLight n config xTarget yTarget zTarget := by
        apply getLight_toggleLight_diff n config xLine yLine zLine xTarget yTarget zTarget wf
        intro hxyz
        rcases hxyz with ⟨_, hyEq, hzEq⟩
        cases hne with
        | inl hyNe => exact hyNe hyEq
        | inr hzNe => exact hzNe hzEq
      have wf' : WellFormed n (toggleLight n config xLine yLine zLine) :=
        toggleLight_preserves_WellFormed_any n config wf xLine yLine zLine
      rw [ih _ wf', hstep]

theorem foldl_toggleX_tail_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (xTarget y z : Nat)
    (hneq : ∀ xLine, xLine ∈ l → xLine ≠ xTarget) :
    getLight n (l.foldl (fun cfg xLine => toggleLight n cfg xLine y z) config) xTarget y z =
      getLight n config xTarget y z := by
  induction l generalizing config wf with
  | nil =>
      rfl
  | cons xLine l ih =>
      simp only [List.foldl_cons]
      have hxNe : xLine ≠ xTarget := hneq xLine (by simp)
      have hstep :
          getLight n (toggleLight n config xLine y z) xTarget y z =
            getLight n config xTarget y z := by
        apply getLight_toggleLight_diff n config xLine y z xTarget y z wf
        intro hxyz
        exact hxNe hxyz.1
      have wf' : WellFormed n (toggleLight n config xLine y z) :=
        toggleLight_preserves_WellFormed_any n config wf xLine y z
      rw [ih _ wf' (by
        intro xLine' hxMem
        exact hneq xLine' (by simp [hxMem])), hstep]

theorem foldl_toggleX_same_flips_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (xTarget y z : Nat)
    (hx : xTarget < n) (hy : y < n) (hz : z < n)
    (hnodup : List.Nodup l) (hmem : xTarget ∈ l) :
    getLight n (l.foldl (fun cfg xLine => toggleLight n cfg xLine y z) config) xTarget y z =
      ((getLight n config xTarget y z) + 1) % 2 := by
  induction l generalizing config wf with
  | nil =>
      cases hmem
  | cons xLine l ih =>
      cases hnodup with
      | cons hnotmem hnodupTail =>
          simp at hmem
          simp only [List.foldl_cons]
          by_cases hEq : xLine = xTarget
          · subst xLine
            have hstep :
                getLight n (toggleLight n config xTarget y z) xTarget y z =
                  ((getLight n config xTarget y z) + 1) % 2 := by
              exact getLight_toggleLight_same n config xTarget y z wf hx hy hz
            have wf' : WellFormed n (toggleLight n config xTarget y z) :=
              toggleLight_preserves_WellFormed n config wf xTarget y z hx hy hz
            rw [foldl_toggleX_tail_preserves_cell n (toggleLight n config xTarget y z) wf' l xTarget y z
              (by
                intro xLine hxMem
                intro hxEq
                exact hnotmem xLine hxMem hxEq.symm), hstep]
          · have hstep :
              getLight n (toggleLight n config xLine y z) xTarget y z =
                getLight n config xTarget y z := by
              apply getLight_toggleLight_diff n config xLine y z xTarget y z wf
              intro hxyz
              exact hEq hxyz.1
            have wf' : WellFormed n (toggleLight n config xLine y z) :=
              toggleLight_preserves_WellFormed_any n config wf xLine y z
            rw [ih _ wf' hnodupTail (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h), hstep]

theorem getLight_applyMoveX_same_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n) :
    getLight n (applyMove n ⟨Direction.x, y, z⟩ config) x y z =
      ((getLight n config x y z) + 1) % 2 := by
  have hmem : x ∈ List.range n := by
    simpa using hx
  simpa [applyMove] using foldl_toggleX_same_flips_cell n config wf (List.range n) x y z hx hy hz List.nodup_range hmem

theorem getLight_applyMoveX_diff_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v x y z : Nat)
    (hne : u ≠ y ∨ v ≠ z) :
    getLight n (applyMove n ⟨Direction.x, u, v⟩ config) x y z =
      getLight n config x y z := by
  simpa [applyMove] using foldl_toggleX_other_preserves_cell n config wf (List.range n) x u v y z hne

theorem foldl_toggleY_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (xLine yTarget zLine xTarget zTarget : Nat)
    (hne : xLine ≠ xTarget ∨ zLine ≠ zTarget) :
    getLight n (l.foldl (fun cfg yLine => toggleLight n cfg xLine yLine zLine) config) xTarget yTarget zTarget =
      getLight n config xTarget yTarget zTarget := by
  induction l generalizing config wf with
  | nil =>
      rfl
  | cons yLine l ih =>
      simp only [List.foldl_cons]
      have hstep :
          getLight n (toggleLight n config xLine yLine zLine) xTarget yTarget zTarget =
            getLight n config xTarget yTarget zTarget := by
        apply getLight_toggleLight_diff n config xLine yLine zLine xTarget yTarget zTarget wf
        intro hxyz
        rcases hxyz with ⟨hxEq, _, hzEq⟩
        cases hne with
        | inl hxNe => exact hxNe hxEq
        | inr hzNe => exact hzNe hzEq
      have wf' : WellFormed n (toggleLight n config xLine yLine zLine) :=
        toggleLight_preserves_WellFormed_any n config wf xLine yLine zLine
      rw [ih _ wf', hstep]

theorem foldl_toggleY_tail_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (x y z : Nat)
    (hneq : ∀ yLine, yLine ∈ l → yLine ≠ y) :
    getLight n (l.foldl (fun cfg yLine => toggleLight n cfg x yLine z) config) x y z =
      getLight n config x y z := by
  induction l generalizing config wf with
  | nil =>
      rfl
  | cons yLine l ih =>
      simp only [List.foldl_cons]
      have hyNe : yLine ≠ y := hneq yLine (by simp)
      have hstep :
          getLight n (toggleLight n config x yLine z) x y z =
            getLight n config x y z := by
        apply getLight_toggleLight_diff n config x yLine z x y z wf
        intro hxyz
        exact hyNe hxyz.2.1
      have wf' : WellFormed n (toggleLight n config x yLine z) :=
        toggleLight_preserves_WellFormed_any n config wf x yLine z
      rw [ih _ wf' (by
        intro yLine' hyMem
        exact hneq yLine' (by simp [hyMem])), hstep]

theorem foldl_toggleY_same_flips_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (x y z : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n)
    (hnodup : List.Nodup l) (hmem : y ∈ l) :
    getLight n (l.foldl (fun cfg yLine => toggleLight n cfg x yLine z) config) x y z =
      ((getLight n config x y z) + 1) % 2 := by
  induction l generalizing config wf with
  | nil =>
      cases hmem
  | cons yLine l ih =>
      cases hnodup with
      | cons hnotmem hnodupTail =>
          simp at hmem
          simp only [List.foldl_cons]
          by_cases hEq : yLine = y
          · subst yLine
            have hstep :
                getLight n (toggleLight n config x y z) x y z =
                  ((getLight n config x y z) + 1) % 2 := by
              exact getLight_toggleLight_same n config x y z wf hx hy hz
            have wf' : WellFormed n (toggleLight n config x y z) :=
              toggleLight_preserves_WellFormed n config wf x y z hx hy hz
            rw [foldl_toggleY_tail_preserves_cell n (toggleLight n config x y z) wf' l x y z
              (by
                intro yLine hyMem
                intro hyEq
                exact hnotmem yLine hyMem hyEq.symm), hstep]
          · have hstep :
              getLight n (toggleLight n config x yLine z) x y z =
                getLight n config x y z := by
              apply getLight_toggleLight_diff n config x yLine z x y z wf
              intro hxyz
              exact hEq hxyz.2.1
            have wf' : WellFormed n (toggleLight n config x yLine z) :=
              toggleLight_preserves_WellFormed_any n config wf x yLine z
            rw [ih _ wf' hnodupTail (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h), hstep]

theorem getLight_applyMoveY_same_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n) :
    getLight n (applyMove n ⟨Direction.y, x, z⟩ config) x y z =
      ((getLight n config x y z) + 1) % 2 := by
  have hmem : y ∈ List.range n := by
    simpa using hy
  simpa [applyMove] using foldl_toggleY_same_flips_cell n config wf (List.range n) x y z hx hy hz List.nodup_range hmem

theorem getLight_applyMoveY_diff_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v x y z : Nat)
    (hne : u ≠ x ∨ v ≠ z) :
    getLight n (applyMove n ⟨Direction.y, u, v⟩ config) x y z =
      getLight n config x y z := by
  simpa [applyMove] using foldl_toggleY_other_preserves_cell n config wf (List.range n) u y v x z hne

theorem foldl_toggleZ_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (xLine yLine zTarget xTarget yTarget : Nat)
    (hne : xLine ≠ xTarget ∨ yLine ≠ yTarget) :
    getLight n (l.foldl (fun cfg zLine => toggleLight n cfg xLine yLine zLine) config) xTarget yTarget zTarget =
      getLight n config xTarget yTarget zTarget := by
  induction l generalizing config wf with
  | nil =>
      rfl
  | cons zLine l ih =>
      simp only [List.foldl_cons]
      have hstep :
          getLight n (toggleLight n config xLine yLine zLine) xTarget yTarget zTarget =
            getLight n config xTarget yTarget zTarget := by
        apply getLight_toggleLight_diff n config xLine yLine zLine xTarget yTarget zTarget wf
        intro hxyz
        rcases hxyz with ⟨hxEq, hyEq, _⟩
        cases hne with
        | inl hxNe => exact hxNe hxEq
        | inr hyNe => exact hyNe hyEq
      have wf' : WellFormed n (toggleLight n config xLine yLine zLine) :=
        toggleLight_preserves_WellFormed_any n config wf xLine yLine zLine
      rw [ih _ wf', hstep]

theorem foldl_toggleZ_tail_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (x y z : Nat)
    (hneq : ∀ zLine, zLine ∈ l → zLine ≠ z) :
    getLight n (l.foldl (fun cfg zLine => toggleLight n cfg x y zLine) config) x y z =
      getLight n config x y z := by
  induction l generalizing config wf with
  | nil =>
      rfl
  | cons zLine l ih =>
      simp only [List.foldl_cons]
      have hzNe : zLine ≠ z := hneq zLine (by simp)
      have hstep :
          getLight n (toggleLight n config x y zLine) x y z =
            getLight n config x y z := by
        apply getLight_toggleLight_diff n config x y zLine x y z wf
        intro hxyz
        exact hzNe hxyz.2.2
      have wf' : WellFormed n (toggleLight n config x y zLine) :=
        toggleLight_preserves_WellFormed_any n config wf x y zLine
      rw [ih _ wf' (by
        intro zLine' hzMem
        exact hneq zLine' (by simp [hzMem])), hstep]

theorem foldl_toggleZ_same_flips_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (l : List Nat)
    (x y z : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n)
    (hnodup : List.Nodup l) (hmem : z ∈ l) :
    getLight n (l.foldl (fun cfg zLine => toggleLight n cfg x y zLine) config) x y z =
      ((getLight n config x y z) + 1) % 2 := by
  induction l generalizing config wf with
  | nil =>
      cases hmem
  | cons zLine l ih =>
      cases hnodup with
      | cons hnotmem hnodupTail =>
          simp at hmem
          simp only [List.foldl_cons]
          by_cases hEq : zLine = z
          · subst zLine
            have hstep :
                getLight n (toggleLight n config x y z) x y z =
                  ((getLight n config x y z) + 1) % 2 := by
              exact getLight_toggleLight_same n config x y z wf hx hy hz
            have wf' : WellFormed n (toggleLight n config x y z) :=
              toggleLight_preserves_WellFormed n config wf x y z hx hy hz
            rw [foldl_toggleZ_tail_preserves_cell n (toggleLight n config x y z) wf' l x y z
              (by
                intro zLine hzMem
                intro hzEq
                exact hnotmem zLine hzMem hzEq.symm), hstep]
          · have hstep :
              getLight n (toggleLight n config x y zLine) x y z =
                getLight n config x y z := by
              apply getLight_toggleLight_diff n config x y zLine x y z wf
              intro hxyz
              exact hEq hxyz.2.2
            have wf' : WellFormed n (toggleLight n config x y zLine) :=
              toggleLight_preserves_WellFormed_any n config wf x y zLine
            rw [ih _ wf' hnodupTail (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h), hstep]

theorem getLight_applyMoveZ_same_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n) :
    getLight n (applyMove n ⟨Direction.z, x, y⟩ config) x y z =
      ((getLight n config x y z) + 1) % 2 := by
  have hmem : z ∈ List.range n := by
    simpa using hz
  simpa [applyMove] using foldl_toggleZ_same_flips_cell n config wf (List.range n) x y z hx hy hz List.nodup_range hmem

theorem getLight_applyMoveZ_diff_any (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v x y z : Nat)
    (hne : u ≠ x ∨ v ≠ y) :
    getLight n (applyMove n ⟨Direction.z, u, v⟩ config) x y z =
      getLight n config x y z := by
  simpa [applyMove] using foldl_toggleZ_other_preserves_cell n config wf (List.range n) u v z x y hne

def moveParity {n : Nat} (target : Move n) : List (Move n) → Nat
  | [] => 0
  | move :: moves => ((if move = target then 1 else 0) + moveParity target moves) % 2

def xMove {n : Nat} (y z : Nat) : Move n := ⟨Direction.x, y, z⟩

def yMove {n : Nat} (x z : Nat) : Move n := ⟨Direction.y, x, z⟩

def zMove {n : Nat} (x y : Nat) : Move n := ⟨Direction.z, x, y⟩

def xParity {n : Nat} (moves : List (Move n)) (y z : Nat) : Nat :=
  moveParity (xMove y z) moves

def yParity {n : Nat} (moves : List (Move n)) (x z : Nat) : Nat :=
  moveParity (yMove x z) moves

def zParity {n : Nat} (moves : List (Move n)) (x y : Nat) : Nat :=
  moveParity (zMove x y) moves

theorem moveParity_lt_two {n : Nat} (target : Move n) (moves : List (Move n)) :
    moveParity target moves < 2 := by
  induction moves with
  | nil =>
      simp [moveParity]
  | cons move moves ih =>
      simp [moveParity]
      omega

theorem getLight_applyMoves_formula (n : Nat) (config : Config n)
    (wf : WellFormed n config) (moves : List (Move n))
    (x y z : Nat) (hx : x < n) (hy : y < n) (hz : z < n) :
    getLight n (applyMoves n moves config) x y z =
      (getLight n config x y z + xParity moves y z + yParity moves x z + zParity moves x y) % 2 := by
  induction moves generalizing config wf with
  | nil =>
      simp [applyMoves, xParity, yParity, zParity, moveParity]
      have hcell : getLight n config x y z < 2 := by
        simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
      omega
  | cons move moves ih =>
      have wf' : WellFormed n (applyMove n move config) :=
        applyMove_preserves_WellFormed n move config wf
      have ih' := ih (applyMove n move config) wf'
      have hrec :
          getLight n (List.foldl (fun cfg m => applyMove n m cfg) (applyMove n move config) moves) x y z =
            (getLight n (applyMove n move config) x y z + xParity moves y z + yParity moves x z + zParity moves x y) % 2 := by
        simpa [applyMoves] using ih'
      simp [applyMoves]
      rw [hrec]
      cases move with
      | mk dir u v =>
          cases dir
          · by_cases hm : (⟨Direction.x, u, v⟩ : Move n) = xMove y z
            · cases hm
              rw [getLight_applyMoveX_same_any n config wf x y z hx hy hz]
              have hcell : getLight n config x y z < 2 := by
                simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
              have hpX : xParity moves y z < 2 := moveParity_lt_two (xMove y z) moves
              have hpY : yParity moves x z < 2 := moveParity_lt_two (yMove x z) moves
              have hpZ : zParity moves x y < 2 := moveParity_lt_two (zMove x y) moves
              simp [xParity, yParity, zParity, xMove, yMove, zMove, moveParity]
              omega
            · have hne : u ≠ y ∨ v ≠ z := by
                by_cases hu : u = y
                · by_cases hv : v = z
                  · exfalso
                    apply hm
                    cases hu
                    cases hv
                    rfl
                  · exact Or.inr hv
                · exact Or.inl hu
              rw [getLight_applyMoveX_diff_any n config wf u v x y z hne]
              have hcell : getLight n config x y z < 2 := by
                simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
              have hpX : xParity moves y z < 2 := moveParity_lt_two (xMove y z) moves
              have hpY : yParity moves x z < 2 := moveParity_lt_two (yMove x z) moves
              have hpZ : zParity moves x y < 2 := moveParity_lt_two (zMove x y) moves
              have hneqTarget : ¬ (u = y ∧ v = z) := by
                intro hEq'
                cases hne with
                | inl huNe => exact huNe hEq'.1
                | inr hvNe => exact hvNe hEq'.2
              simp [xParity, yParity, zParity, xMove, yMove, zMove, moveParity, hneqTarget]
              omega
          · by_cases hm : (⟨Direction.y, u, v⟩ : Move n) = yMove x z
            · cases hm
              rw [getLight_applyMoveY_same_any n config wf x y z hx hy hz]
              have hcell : getLight n config x y z < 2 := by
                simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
              have hpX : xParity moves y z < 2 := moveParity_lt_two (xMove y z) moves
              have hpY : yParity moves x z < 2 := moveParity_lt_two (yMove x z) moves
              have hpZ : zParity moves x y < 2 := moveParity_lt_two (zMove x y) moves
              simp [xParity, yParity, zParity, xMove, yMove, zMove, moveParity]
              omega
            · have hne : u ≠ x ∨ v ≠ z := by
                by_cases hu : u = x
                · by_cases hv : v = z
                  · exfalso
                    apply hm
                    cases hu
                    cases hv
                    rfl
                  · exact Or.inr hv
                · exact Or.inl hu
              rw [getLight_applyMoveY_diff_any n config wf u v x y z hne]
              have hcell : getLight n config x y z < 2 := by
                simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
              have hpX : xParity moves y z < 2 := moveParity_lt_two (xMove y z) moves
              have hpY : yParity moves x z < 2 := moveParity_lt_two (yMove x z) moves
              have hpZ : zParity moves x y < 2 := moveParity_lt_two (zMove x y) moves
              have hneqTarget : ¬ (u = x ∧ v = z) := by
                intro hEq'
                cases hne with
                | inl huNe => exact huNe hEq'.1
                | inr hvNe => exact hvNe hEq'.2
              simp [xParity, yParity, zParity, xMove, yMove, zMove, moveParity, hneqTarget]
              omega
          · by_cases hm : (⟨Direction.z, u, v⟩ : Move n) = zMove x y
            · cases hm
              rw [getLight_applyMoveZ_same_any n config wf x y z hx hy hz]
              have hcell : getLight n config x y z < 2 := by
                simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
              have hpX : xParity moves y z < 2 := moveParity_lt_two (xMove y z) moves
              have hpY : yParity moves x z < 2 := moveParity_lt_two (yMove x z) moves
              have hpZ : zParity moves x y < 2 := moveParity_lt_two (zMove x y) moves
              simp [xParity, yParity, zParity, xMove, yMove, zMove, moveParity]
              omega
            · have hne : u ≠ x ∨ v ≠ y := by
                by_cases hu : u = x
                · by_cases hv : v = y
                  · exfalso
                    apply hm
                    cases hu
                    cases hv
                    rfl
                  · exact Or.inr hv
                · exact Or.inl hu
              rw [getLight_applyMoveZ_diff_any n config wf u v x y z hne]
              have hcell : getLight n config x y z < 2 := by
                simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
              have hpX : xParity moves y z < 2 := moveParity_lt_two (xMove y z) moves
              have hpY : yParity moves x z < 2 := moveParity_lt_two (yMove x z) moves
              have hpZ : zParity moves x y < 2 := moveParity_lt_two (zMove x y) moves
              have hneqTarget : ¬ (u = x ∧ v = y) := by
                intro hEq'
                cases hne with
                | inl huNe => exact huNe hEq'.1
                | inr hvNe => exact hvNe hEq'.2
              simp [xParity, yParity, zParity, xMove, yMove, zMove, moveParity, hneqTarget]
              omega

theorem processXRow_other_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) (hne : uLine ≠ uTarget) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg 0 uLine vLine = 1 then
          applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
        else cfg) config)
      0 uTarget vTarget =
    getLight n config 0 uTarget vTarget := by
  induction List.range n generalizing config with
  | nil =>
      rfl
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config 0 uLine vLine = 1
      · have hcfg :
          getLight n (applyMove n ⟨Direction.x, uLine, vLine⟩ config) 0 uTarget vTarget =
            getLight n config 0 uTarget vTarget := by
          exact getLight_applyMoveX_diff n config wf uLine vLine uTarget vTarget hu hv (Or.inl hne)
        have hwf' : WellFormed n (applyMove n ⟨Direction.x, uLine, vLine⟩ config) :=
          applyMove_preserves_WellFormed n ⟨Direction.x, uLine, vLine⟩ config wf
        simp [hlit]
        rw [ih _ hwf', hcfg]
      · simp [hlit]
        rw [ih _ wf]

theorem processXRow_same_clears_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg 0 uTarget vLine = 1 then
          applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg
        else cfg) config)
      0 uTarget vTarget = 0 := by
  have zero_stays : ∀ l cfg, WellFormed n cfg →
      getLight n cfg 0 uTarget vTarget = 0 →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg 0 uTarget vLine = 1 then
            applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg
          else cfg) cfg l)
        0 uTarget vTarget = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ hzero
        simpa using hzero
    | cons vLine l ih =>
        intro cfg hwf hzero
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg 0 uTarget vLine = 1
        · by_cases hEq : vLine = vTarget
          · subst hEq
            rw [hzero] at hlit
            cases hlit
          · have hwf' : WellFormed n (applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.x, uTarget, vLine⟩ cfg hwf
            have hzero' :
                getLight n (applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg) 0 uTarget vTarget = 0 := by
              rw [getLight_applyMoveX_diff n cfg hwf uTarget vLine uTarget vTarget hu hv (Or.inr hEq)]
              exact hzero
            simp [hlit]
            exact ih _ hwf' hzero'
        · simp [hlit]
          exact ih _ hwf hzero
  have clears_mem : ∀ l cfg, WellFormed n cfg → vTarget ∈ l →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg 0 uTarget vLine = 1 then
            applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg
          else cfg) cfg l)
        0 uTarget vTarget = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ hmem
        cases hmem
    | cons vLine l ih =>
        intro cfg hwf hmem
        simp at hmem
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg 0 uTarget vLine = 1
        · by_cases hEq : vLine = vTarget
          · subst vLine
            have hwf' : WellFormed n (applyMove n ⟨Direction.x, uTarget, vTarget⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.x, uTarget, vTarget⟩ cfg hwf
            have hzero :
                getLight n (applyMove n ⟨Direction.x, uTarget, vTarget⟩ cfg) 0 uTarget vTarget = 0 := by
              rw [getLight_applyMoveX_same n cfg hwf uTarget vTarget hu hv]
              omega
            simp [hlit]
            exact zero_stays l _ hwf' hzero
          · have hwf' : WellFormed n (applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.x, uTarget, vLine⟩ cfg hwf
            simp [hlit]
            exact ih _ hwf' (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h)
        · by_cases hEq : vLine = vTarget
          · subst vLine
            have hzero : getLight n cfg 0 uTarget vTarget = 0 := by
              have h0 : 0 < n := by omega
              have hlt : getLight n cfg 0 uTarget vTarget < 2 := by
                simpa [getLight, h0, hu, hv] using hwf.2.2.2 0 uTarget vTarget h0 hu hv
              omega
            simp [hlit]
            exact zero_stays l _ hwf hzero
          · simp [hlit]
            exact ih _ hwf (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h)
  have hvMem : vTarget ∈ List.range n := by
    simpa using hv
  exact clears_mem (List.range n) config wf hvMem

theorem processXRow_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine : Nat) :
    WellFormed n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg 0 uLine vLine = 1 then
          applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
        else cfg) config) := by
  induction List.range n generalizing config with
  | nil =>
      simpa using wf
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config 0 uLine vLine = 1
      · simp [hlit]
        apply ih
        exact applyMove_preserves_WellFormed n ⟨Direction.x, uLine, vLine⟩ config wf
      · simp [hlit]
        exact ih _ wf

theorem processXSurface_other_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    ∀ l, (∀ uLine, uLine ∈ l → uLine ≠ uTarget) →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg 0 uLine vLine = 1 then
              applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
            else cfg) cfg)
          config l)
        0 uTarget vTarget =
      getLight n config 0 uTarget vTarget := by
  intro l
  induction l generalizing config with
  | nil =>
      intro _
      rfl
  | cons uLine l ih =>
      intro hneq
      simp only [List.foldl_cons]
      have huLineNe : uLine ≠ uTarget := hneq uLine (by simp)
      have hfront :
          getLight n
            ((List.range n).foldl (fun cfg vLine =>
              if getLight n cfg 0 uLine vLine = 1 then
                applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
              else cfg) config)
            0 uTarget vTarget =
          getLight n config 0 uTarget vTarget :=
        processXRow_other_preserves_front n config wf uLine uTarget vTarget hu hv huLineNe
      have hwf' : WellFormed n
          ((List.range n).foldl (fun cfg vLine =>
            if getLight n cfg 0 uLine vLine = 1 then
              applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
            else cfg) config) :=
        processXRow_preserves_WellFormed n config wf uLine
      rw [ih _ hwf' (by
        intro u huMem
        exact hneq u (by simp [huMem])), hfront]

theorem processXSurface_clears_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    getLight n (processXSurface n config) 0 uTarget vTarget = 0 := by
  have clears_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → uTarget ∈ l →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg 0 uLine vLine = 1 then
              applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
            else cfg) cfg)
          cfg l)
        0 uTarget vTarget = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons uLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : uLine = uTarget
            · subst uLine
              have hwfRow : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg 0 uTarget vLine = 1 then
                      applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg
                    else cfg) cfg) :=
                processXRow_preserves_WellFormed n cfg hwf uTarget
              have hclear :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg 0 uTarget vLine = 1 then
                        applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg
                      else cfg) cfg)
                    0 uTarget vTarget = 0 :=
                processXRow_same_clears_front n cfg hwf uTarget vTarget hu hv
              have hpres := processXSurface_other_preserves_front n
                ((List.range n).foldl (fun cfg vLine =>
                  if getLight n cfg 0 uTarget vLine = 1 then
                    applyMove n ⟨Direction.x, uTarget, vLine⟩ cfg
                  else cfg) cfg)
                hwfRow uTarget vTarget hu hv l
                (by
                  intro u huMem
                  intro huEq
                  exact hnotmem u huMem huEq.symm)
              rw [hpres, hclear]
            · have hfront :
                getLight n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg 0 uLine vLine = 1 then
                      applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
                    else cfg) cfg)
                  0 uTarget vTarget =
                getLight n cfg 0 uTarget vTarget :=
              processXRow_other_preserves_front n cfg hwf uLine uTarget vTarget hu hv hEq
              have hwfRow : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg 0 uLine vLine = 1 then
                      applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
                    else cfg) cfg) :=
                processXRow_preserves_WellFormed n cfg hwf uLine
              have hmemTail : uTarget ∈ l := by
                cases hmem with
                | inl h => exact False.elim (hEq h.symm)
                | inr h => exact h
              simpa using ih _ hwfRow hnodupTail hmemTail
  have huMem : uTarget ∈ List.range n := by
    simpa using hu
  simpa [processXSurface, processSurface] using clears_mem (List.range n) config wf List.nodup_range huMem

theorem processSurface_clears_x_face (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v : Nat) (hu : u < n) (hv : v < n) :
    getLight n (processSurface n Direction.x config) 0 u v = 0 := by
  simpa [processXSurface] using processXSurface_clears_front n config wf u v hu hv

theorem processXRow_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine xTarget yTarget zTarget : Nat)
    (hne : uLine ≠ yTarget) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg 0 uLine vLine = 1 then
          applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
        else cfg) config)
      xTarget yTarget zTarget =
    getLight n config xTarget yTarget zTarget := by
  induction List.range n generalizing config with
  | nil =>
      rfl
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config 0 uLine vLine = 1
      · have hcfg :
          getLight n (applyMove n ⟨Direction.x, uLine, vLine⟩ config) xTarget yTarget zTarget =
            getLight n config xTarget yTarget zTarget := by
          exact getLight_applyMoveX_diff_any n config wf uLine vLine xTarget yTarget zTarget (Or.inl hne)
        have hwf' : WellFormed n (applyMove n ⟨Direction.x, uLine, vLine⟩ config) :=
          applyMove_preserves_WellFormed n ⟨Direction.x, uLine, vLine⟩ config wf
        simp [hlit]
        rw [ih _ hwf', hcfg]
      · simp [hlit]
        rw [ih _ wf]

theorem processXRow_same_updates_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (hx : xTarget < n) (hy : yTarget < n) (hz : zTarget < n) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg 0 yTarget vLine = 1 then
          applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
        else cfg) config)
      xTarget yTarget zTarget =
    (getLight n config xTarget yTarget zTarget + getLight n config 0 yTarget zTarget) % 2 := by
  have other_v_preserves_cell : ∀ l cfg, WellFormed n cfg →
      (∀ vLine, vLine ∈ l → vLine ≠ zTarget) →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg 0 yTarget vLine = 1 then
            applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
          else cfg) cfg l)
        xTarget yTarget zTarget =
      getLight n cfg xTarget yTarget zTarget := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _
        rfl
    | cons vLine l ih =>
        intro cfg hwf hneq
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg 0 yTarget vLine = 1
        · have hvNe : vLine ≠ zTarget := hneq vLine (by simp)
          have hcfg :
              getLight n (applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg) xTarget yTarget zTarget =
                getLight n cfg xTarget yTarget zTarget := by
            exact getLight_applyMoveX_diff_any n cfg hwf yTarget vLine xTarget yTarget zTarget (Or.inr hvNe)
          have hwf' : WellFormed n (applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg) :=
            applyMove_preserves_WellFormed n ⟨Direction.x, yTarget, vLine⟩ cfg hwf
          simp [hlit]
          rw [ih _ hwf' (by
            intro vLine' hvMem
            exact hneq vLine' (by simp [hvMem])), hcfg]
        · simp [hlit]
          rw [ih _ hwf (by
            intro vLine' hvMem
            exact hneq vLine' (by simp [hvMem]))]
  have updates_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → zTarget ∈ l →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg 0 yTarget vLine = 1 then
            applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
          else cfg) cfg l)
        xTarget yTarget zTarget =
      (getLight n cfg xTarget yTarget zTarget + getLight n cfg 0 yTarget zTarget) % 2 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons vLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : vLine = zTarget
            · subst vLine
              by_cases hlit : getLight n cfg 0 yTarget zTarget = 1
              · have hstep :
                    getLight n (applyMove n ⟨Direction.x, yTarget, zTarget⟩ cfg) xTarget yTarget zTarget =
                      ((getLight n cfg xTarget yTarget zTarget) + 1) % 2 := by
                  exact getLight_applyMoveX_same_any n cfg hwf xTarget yTarget zTarget hx hy hz
                have hwf' : WellFormed n (applyMove n ⟨Direction.x, yTarget, zTarget⟩ cfg) :=
                  applyMove_preserves_WellFormed n ⟨Direction.x, yTarget, zTarget⟩ cfg hwf
                have htail :
                    getLight n
                      (List.foldl (fun cfg vLine =>
                        if getLight n cfg 0 yTarget vLine = 1 then
                          applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
                        else cfg)
                        (applyMove n ⟨Direction.x, yTarget, zTarget⟩ cfg) l)
                      xTarget yTarget zTarget =
                    getLight n (applyMove n ⟨Direction.x, yTarget, zTarget⟩ cfg) xTarget yTarget zTarget :=
                  other_v_preserves_cell l _ hwf' (by
                    intro vLine hvMem
                    intro hvEq
                    exact hnotmem vLine hvMem hvEq.symm)
                simp [hlit]
                rw [htail, hstep]
              · have htail :
                    getLight n
                      (List.foldl (fun cfg vLine =>
                        if getLight n cfg 0 yTarget vLine = 1 then
                          applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
                        else cfg) cfg l)
                      xTarget yTarget zTarget =
                    getLight n cfg xTarget yTarget zTarget :=
                  other_v_preserves_cell l _ hwf (by
                    intro vLine hvMem
                    intro hvEq
                    exact hnotmem vLine hvMem hvEq.symm)
                simp [hlit]
                rw [htail]
                have hfrontVal : getLight n cfg 0 yTarget zTarget = 0 := by
                  have h0 : 0 < n := by omega
                  have hfront : getLight n cfg 0 yTarget zTarget < 2 := by
                    simpa [getLight, h0, hy, hz] using hwf.2.2.2 0 yTarget zTarget h0 hy hz
                  omega
                rw [hfrontVal]
                have hcell : getLight n cfg xTarget yTarget zTarget < 2 := by
                  simpa [getLight, hx, hy, hz] using hwf.2.2.2 xTarget yTarget zTarget hx hy hz
                omega
            · by_cases hlit : getLight n cfg 0 yTarget vLine = 1
              · have hcfgTarget :
                    getLight n (applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg) xTarget yTarget zTarget =
                      getLight n cfg xTarget yTarget zTarget := by
                  exact getLight_applyMoveX_diff_any n cfg hwf yTarget vLine xTarget yTarget zTarget (Or.inr hEq)
                have hcfgFront :
                    getLight n (applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg) 0 yTarget zTarget =
                      getLight n cfg 0 yTarget zTarget := by
                  exact getLight_applyMoveX_diff n cfg hwf yTarget vLine yTarget zTarget hy hz (Or.inr hEq)
                have hwf' : WellFormed n (applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg) :=
                  applyMove_preserves_WellFormed n ⟨Direction.x, yTarget, vLine⟩ cfg hwf
                have hmemTail : zTarget ∈ l := by
                  cases hmem with
                  | inl h => exact False.elim (hEq h.symm)
                  | inr h => exact h
                simp [hlit]
                rw [ih _ hwf' hnodupTail hmemTail, hcfgTarget, hcfgFront]
              · have hmemTail : zTarget ∈ l := by
                  cases hmem with
                  | inl h => exact False.elim (hEq h.symm)
                  | inr h => exact h
                simp [hlit]
                exact ih _ hwf hnodupTail hmemTail
  have hmem : zTarget ∈ List.range n := by
    simpa using hz
  exact updates_mem (List.range n) config wf List.nodup_range hmem

theorem processXSurface_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (_hy : yTarget < n) :
    ∀ l, (∀ uLine, uLine ∈ l → uLine ≠ yTarget) →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg 0 uLine vLine = 1 then
              applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
            else cfg) cfg)
          config l)
        xTarget yTarget zTarget =
      getLight n config xTarget yTarget zTarget := by
  intro l
  induction l generalizing config with
  | nil =>
      intro _
      rfl
  | cons uLine l ih =>
      intro hneq
      simp only [List.foldl_cons]
      have huLineNe : uLine ≠ yTarget := hneq uLine (by simp)
      have hcell :
          getLight n
            ((List.range n).foldl (fun cfg vLine =>
              if getLight n cfg 0 uLine vLine = 1 then
                applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
              else cfg) config)
            xTarget yTarget zTarget =
          getLight n config xTarget yTarget zTarget :=
        processXRow_other_preserves_cell n config wf uLine xTarget yTarget zTarget huLineNe
      have hwf' : WellFormed n
          ((List.range n).foldl (fun cfg vLine =>
            if getLight n cfg 0 uLine vLine = 1 then
              applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
            else cfg) config) :=
        processXRow_preserves_WellFormed n config wf uLine
      rw [ih _ hwf' (by
        intro u huMem
        exact hneq u (by simp [huMem])), hcell]

theorem processXSurface_updates_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (hx : xTarget < n) (hy : yTarget < n) (hz : zTarget < n) :
    getLight n (processXSurface n config) xTarget yTarget zTarget =
      (getLight n config xTarget yTarget zTarget + getLight n config 0 yTarget zTarget) % 2 := by
  have updates_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → yTarget ∈ l →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg 0 uLine vLine = 1 then
              applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
            else cfg) cfg)
          cfg l)
        xTarget yTarget zTarget =
      (getLight n cfg xTarget yTarget zTarget + getLight n cfg 0 yTarget zTarget) % 2 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons uLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : uLine = yTarget
            · subst uLine
              have hrow :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg 0 yTarget vLine = 1 then
                        applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget =
                  (getLight n cfg xTarget yTarget zTarget + getLight n cfg 0 yTarget zTarget) % 2 :=
                processXRow_same_updates_cell n cfg hwf xTarget yTarget zTarget hx hy hz
              have hwf' : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg 0 yTarget vLine = 1 then
                      applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
                    else cfg) cfg) :=
                processXRow_preserves_WellFormed n cfg hwf yTarget
              have htail :
                  getLight n
                    (List.foldl (fun cfg uLine =>
                      (List.range n).foldl (fun cfg vLine =>
                        if getLight n cfg 0 uLine vLine = 1 then
                          applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
                        else cfg) cfg)
                      ((List.range n).foldl (fun cfg vLine =>
                        if getLight n cfg 0 yTarget vLine = 1 then
                          applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
                        else cfg) cfg) l)
                    xTarget yTarget zTarget =
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg 0 yTarget vLine = 1 then
                        applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget :=
                processXSurface_other_preserves_cell n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg 0 yTarget vLine = 1 then
                      applyMove n ⟨Direction.x, yTarget, vLine⟩ cfg
                    else cfg) cfg)
                  hwf' xTarget yTarget zTarget hy l
                  (by
                    intro u huMem
                    intro huEq
                    exact hnotmem u huMem huEq.symm)
              exact htail.trans hrow
            · have hcell :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg 0 uLine vLine = 1 then
                        applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget =
                  getLight n cfg xTarget yTarget zTarget :=
                processXRow_other_preserves_cell n cfg hwf uLine xTarget yTarget zTarget hEq
              have hfront :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg 0 uLine vLine = 1 then
                        applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
                      else cfg) cfg)
                    0 yTarget zTarget =
                  getLight n cfg 0 yTarget zTarget :=
                processXRow_other_preserves_cell n cfg hwf uLine 0 yTarget zTarget hEq
              have hwf' : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg 0 uLine vLine = 1 then
                      applyMove n ⟨Direction.x, uLine, vLine⟩ cfg
                    else cfg) cfg) :=
                processXRow_preserves_WellFormed n cfg hwf uLine
              have hmemTail : yTarget ∈ l := by
                cases hmem with
                | inl h => exact False.elim (hEq h.symm)
                | inr h => exact h
              rw [ih _ hwf' hnodupTail hmemTail, hcell, hfront]
  have hmem : yTarget ∈ List.range n := by
    simpa using hy
  simpa [processXSurface, processSurface] using updates_mem (List.range n) config wf List.nodup_range hmem

theorem processYRow_preserves_WellFormed_aux (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine : Nat) :
    WellFormed n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uLine 0 vLine = 1 then
          applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
        else cfg) config) := by
  induction List.range n generalizing config with
  | nil =>
      simpa using wf
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config uLine 0 vLine = 1
      · simp [hlit]
        apply ih
        exact applyMove_preserves_WellFormed n ⟨Direction.y, uLine, vLine⟩ config wf
      · simp [hlit]
        exact ih _ wf

theorem processYRow_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine xTarget yTarget zTarget : Nat)
    (hne : uLine ≠ xTarget) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uLine 0 vLine = 1 then
          applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
        else cfg) config)
      xTarget yTarget zTarget =
    getLight n config xTarget yTarget zTarget := by
  induction List.range n generalizing config with
  | nil =>
      rfl
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config uLine 0 vLine = 1
      · have hcfg :
          getLight n (applyMove n ⟨Direction.y, uLine, vLine⟩ config) xTarget yTarget zTarget =
            getLight n config xTarget yTarget zTarget := by
          exact getLight_applyMoveY_diff_any n config wf uLine vLine xTarget yTarget zTarget (Or.inl hne)
        have hwf' : WellFormed n (applyMove n ⟨Direction.y, uLine, vLine⟩ config) :=
          applyMove_preserves_WellFormed n ⟨Direction.y, uLine, vLine⟩ config wf
        simp [hlit]
        rw [ih _ hwf', hcfg]
      · simp [hlit]
        rw [ih _ wf]

theorem processYRow_same_updates_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (hx : xTarget < n) (hy : yTarget < n) (hz : zTarget < n) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg xTarget 0 vLine = 1 then
          applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
        else cfg) config)
      xTarget yTarget zTarget =
    (getLight n config xTarget yTarget zTarget + getLight n config xTarget 0 zTarget) % 2 := by
  have other_v_preserves_cell : ∀ l cfg, WellFormed n cfg →
      (∀ vLine, vLine ∈ l → vLine ≠ zTarget) →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg xTarget 0 vLine = 1 then
            applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
          else cfg) cfg l)
        xTarget yTarget zTarget =
      getLight n cfg xTarget yTarget zTarget := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _
        rfl
    | cons vLine l ih =>
        intro cfg hwf hneq
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg xTarget 0 vLine = 1
        · have hvNe : vLine ≠ zTarget := hneq vLine (by simp)
          have hcfg :
              getLight n (applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg) xTarget yTarget zTarget =
                getLight n cfg xTarget yTarget zTarget := by
            exact getLight_applyMoveY_diff_any n cfg hwf xTarget vLine xTarget yTarget zTarget (Or.inr hvNe)
          have hwf' : WellFormed n (applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg) :=
            applyMove_preserves_WellFormed n ⟨Direction.y, xTarget, vLine⟩ cfg hwf
          simp [hlit]
          rw [ih _ hwf' (by
            intro vLine' hvMem
            exact hneq vLine' (by simp [hvMem])), hcfg]
        · simp [hlit]
          rw [ih _ hwf (by
            intro vLine' hvMem
            exact hneq vLine' (by simp [hvMem]))]
  have updates_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → zTarget ∈ l →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg xTarget 0 vLine = 1 then
            applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
          else cfg) cfg l)
        xTarget yTarget zTarget =
      (getLight n cfg xTarget yTarget zTarget + getLight n cfg xTarget 0 zTarget) % 2 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons vLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : vLine = zTarget
            · subst vLine
              by_cases hlit : getLight n cfg xTarget 0 zTarget = 1
              · have hstep :
                    getLight n (applyMove n ⟨Direction.y, xTarget, zTarget⟩ cfg) xTarget yTarget zTarget =
                      ((getLight n cfg xTarget yTarget zTarget) + 1) % 2 := by
                  exact getLight_applyMoveY_same_any n cfg hwf xTarget yTarget zTarget hx hy hz
                have hwf' : WellFormed n (applyMove n ⟨Direction.y, xTarget, zTarget⟩ cfg) :=
                  applyMove_preserves_WellFormed n ⟨Direction.y, xTarget, zTarget⟩ cfg hwf
                have htail :
                    getLight n
                      (List.foldl (fun cfg vLine =>
                        if getLight n cfg xTarget 0 vLine = 1 then
                          applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
                        else cfg)
                        (applyMove n ⟨Direction.y, xTarget, zTarget⟩ cfg) l)
                      xTarget yTarget zTarget =
                    getLight n (applyMove n ⟨Direction.y, xTarget, zTarget⟩ cfg) xTarget yTarget zTarget :=
                  other_v_preserves_cell l _ hwf' (by
                    intro vLine hvMem
                    intro hvEq
                    exact hnotmem vLine hvMem hvEq.symm)
                simp [hlit]
                rw [htail, hstep]
              · have htail :
                    getLight n
                      (List.foldl (fun cfg vLine =>
                        if getLight n cfg xTarget 0 vLine = 1 then
                          applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
                        else cfg) cfg l)
                      xTarget yTarget zTarget =
                    getLight n cfg xTarget yTarget zTarget :=
                  other_v_preserves_cell l _ hwf (by
                    intro vLine hvMem
                    intro hvEq
                    exact hnotmem vLine hvMem hvEq.symm)
                simp [hlit]
                rw [htail]
                have hfrontVal : getLight n cfg xTarget 0 zTarget = 0 := by
                  have h0 : 0 < n := by omega
                  have hfront : getLight n cfg xTarget 0 zTarget < 2 := by
                    simpa [getLight, hx, h0, hz] using hwf.2.2.2 xTarget 0 zTarget hx h0 hz
                  omega
                rw [hfrontVal]
                have hcell : getLight n cfg xTarget yTarget zTarget < 2 := by
                  simpa [getLight, hx, hy, hz] using hwf.2.2.2 xTarget yTarget zTarget hx hy hz
                omega
            · by_cases hlit : getLight n cfg xTarget 0 vLine = 1
              · have hcfgTarget :
                    getLight n (applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg) xTarget yTarget zTarget =
                      getLight n cfg xTarget yTarget zTarget := by
                  exact getLight_applyMoveY_diff_any n cfg hwf xTarget vLine xTarget yTarget zTarget (Or.inr hEq)
                have hcfgFront :
                    getLight n (applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg) xTarget 0 zTarget =
                      getLight n cfg xTarget 0 zTarget := by
                  exact getLight_applyMoveY_diff n cfg hwf xTarget vLine xTarget zTarget hx hz (Or.inr hEq)
                have hwf' : WellFormed n (applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg) :=
                  applyMove_preserves_WellFormed n ⟨Direction.y, xTarget, vLine⟩ cfg hwf
                have hmemTail : zTarget ∈ l := by
                  cases hmem with
                  | inl h => exact False.elim (hEq h.symm)
                  | inr h => exact h
                simp [hlit]
                rw [ih _ hwf' hnodupTail hmemTail, hcfgTarget, hcfgFront]
              · have hmemTail : zTarget ∈ l := by
                  cases hmem with
                  | inl h => exact False.elim (hEq h.symm)
                  | inr h => exact h
                simp [hlit]
                exact ih _ hwf hnodupTail hmemTail
  have hmem : zTarget ∈ List.range n := by
    simpa using hz
  exact updates_mem (List.range n) config wf List.nodup_range hmem

theorem processYSurface_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (_hx : xTarget < n) :
    ∀ l, (∀ uLine, uLine ∈ l → uLine ≠ xTarget) →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine 0 vLine = 1 then
              applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
            else cfg) cfg)
          config l)
        xTarget yTarget zTarget =
      getLight n config xTarget yTarget zTarget := by
  intro l
  induction l generalizing config with
  | nil =>
      intro _
      rfl
  | cons uLine l ih =>
      intro hneq
      simp only [List.foldl_cons]
      have huLineNe : uLine ≠ xTarget := hneq uLine (by simp)
      have hcell :
          getLight n
            ((List.range n).foldl (fun cfg vLine =>
              if getLight n cfg uLine 0 vLine = 1 then
                applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
              else cfg) config)
            xTarget yTarget zTarget =
          getLight n config xTarget yTarget zTarget :=
        processYRow_other_preserves_cell n config wf uLine xTarget yTarget zTarget huLineNe
      have hwf' : WellFormed n
          ((List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine 0 vLine = 1 then
              applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
            else cfg) config) :=
        processYRow_preserves_WellFormed_aux n config wf uLine
      rw [ih _ hwf' (by
        intro u huMem
        exact hneq u (by simp [huMem])), hcell]

theorem processYSurface_updates_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (hx : xTarget < n) (hy : yTarget < n) (hz : zTarget < n) :
    getLight n (processYSurface n config) xTarget yTarget zTarget =
      (getLight n config xTarget yTarget zTarget + getLight n config xTarget 0 zTarget) % 2 := by
  have updates_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → xTarget ∈ l →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine 0 vLine = 1 then
              applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
            else cfg) cfg)
          cfg l)
        xTarget yTarget zTarget =
      (getLight n cfg xTarget yTarget zTarget + getLight n cfg xTarget 0 zTarget) % 2 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons uLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : uLine = xTarget
            · subst uLine
              have hrow :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg xTarget 0 vLine = 1 then
                        applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget =
                  (getLight n cfg xTarget yTarget zTarget + getLight n cfg xTarget 0 zTarget) % 2 :=
                processYRow_same_updates_cell n cfg hwf xTarget yTarget zTarget hx hy hz
              have hwf' : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg xTarget 0 vLine = 1 then
                      applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
                    else cfg) cfg) :=
                processYRow_preserves_WellFormed_aux n cfg hwf xTarget
              have htail :
                  getLight n
                    (List.foldl (fun cfg uLine =>
                      (List.range n).foldl (fun cfg vLine =>
                        if getLight n cfg uLine 0 vLine = 1 then
                          applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
                        else cfg) cfg)
                      ((List.range n).foldl (fun cfg vLine =>
                        if getLight n cfg xTarget 0 vLine = 1 then
                          applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
                        else cfg) cfg) l)
                    xTarget yTarget zTarget =
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg xTarget 0 vLine = 1 then
                        applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget :=
                processYSurface_other_preserves_cell n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg xTarget 0 vLine = 1 then
                      applyMove n ⟨Direction.y, xTarget, vLine⟩ cfg
                    else cfg) cfg)
                  hwf' xTarget yTarget zTarget hx l
                  (by
                    intro u huMem
                    intro huEq
                    exact hnotmem u huMem huEq.symm)
              exact htail.trans hrow
            · have hcell :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg uLine 0 vLine = 1 then
                        applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget =
                  getLight n cfg xTarget yTarget zTarget :=
                processYRow_other_preserves_cell n cfg hwf uLine xTarget yTarget zTarget hEq
              have hfront :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg uLine 0 vLine = 1 then
                        applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget 0 zTarget =
                  getLight n cfg xTarget 0 zTarget :=
                processYRow_other_preserves_cell n cfg hwf uLine xTarget 0 zTarget hEq
              have hwf' : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg uLine 0 vLine = 1 then
                      applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
                    else cfg) cfg) :=
                processYRow_preserves_WellFormed_aux n cfg hwf uLine
              have hmemTail : xTarget ∈ l := by
                cases hmem with
                | inl h => exact False.elim (hEq h.symm)
                | inr h => exact h
              rw [ih _ hwf' hnodupTail hmemTail, hcell, hfront]
  have hmem : xTarget ∈ List.range n := by
    simpa using hx
  simpa [processYSurface, processSurface] using updates_mem (List.range n) config wf List.nodup_range hmem

theorem processZRow_preserves_WellFormed_aux (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine : Nat) :
    WellFormed n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uLine vLine 0 = 1 then
          applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
        else cfg) config) := by
  induction List.range n generalizing config with
  | nil =>
      simpa using wf
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config uLine vLine 0 = 1
      · simp [hlit]
        apply ih
        exact applyMove_preserves_WellFormed n ⟨Direction.z, uLine, vLine⟩ config wf
      · simp [hlit]
        exact ih _ wf

theorem processZRow_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine xTarget yTarget zTarget : Nat)
    (hne : uLine ≠ xTarget) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uLine vLine 0 = 1 then
          applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
        else cfg) config)
      xTarget yTarget zTarget =
    getLight n config xTarget yTarget zTarget := by
  induction List.range n generalizing config with
  | nil =>
      rfl
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config uLine vLine 0 = 1
      · have hcfg :
          getLight n (applyMove n ⟨Direction.z, uLine, vLine⟩ config) xTarget yTarget zTarget =
            getLight n config xTarget yTarget zTarget := by
          exact getLight_applyMoveZ_diff_any n config wf uLine vLine xTarget yTarget zTarget (Or.inl hne)
        have hwf' : WellFormed n (applyMove n ⟨Direction.z, uLine, vLine⟩ config) :=
          applyMove_preserves_WellFormed n ⟨Direction.z, uLine, vLine⟩ config wf
        simp [hlit]
        rw [ih _ hwf', hcfg]
      · simp [hlit]
        rw [ih _ wf]

theorem processZRow_same_updates_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (hx : xTarget < n) (hy : yTarget < n) (hz : zTarget < n) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg xTarget vLine 0 = 1 then
          applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
        else cfg) config)
      xTarget yTarget zTarget =
    (getLight n config xTarget yTarget zTarget + getLight n config xTarget yTarget 0) % 2 := by
  have other_v_preserves_cell : ∀ l cfg, WellFormed n cfg →
      (∀ vLine, vLine ∈ l → vLine ≠ yTarget) →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg xTarget vLine 0 = 1 then
            applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
          else cfg) cfg l)
        xTarget yTarget zTarget =
      getLight n cfg xTarget yTarget zTarget := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _
        rfl
    | cons vLine l ih =>
        intro cfg hwf hneq
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg xTarget vLine 0 = 1
        · have hvNe : vLine ≠ yTarget := hneq vLine (by simp)
          have hcfg :
              getLight n (applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg) xTarget yTarget zTarget =
                getLight n cfg xTarget yTarget zTarget := by
            exact getLight_applyMoveZ_diff_any n cfg hwf xTarget vLine xTarget yTarget zTarget (Or.inr hvNe)
          have hwf' : WellFormed n (applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg) :=
            applyMove_preserves_WellFormed n ⟨Direction.z, xTarget, vLine⟩ cfg hwf
          simp [hlit]
          rw [ih _ hwf' (by
            intro vLine' hvMem
            exact hneq vLine' (by simp [hvMem])), hcfg]
        · simp [hlit]
          rw [ih _ hwf (by
            intro vLine' hvMem
            exact hneq vLine' (by simp [hvMem]))]
  have updates_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → yTarget ∈ l →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg xTarget vLine 0 = 1 then
            applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
          else cfg) cfg l)
        xTarget yTarget zTarget =
      (getLight n cfg xTarget yTarget zTarget + getLight n cfg xTarget yTarget 0) % 2 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons vLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : vLine = yTarget
            · subst vLine
              by_cases hlit : getLight n cfg xTarget yTarget 0 = 1
              · have hstep :
                    getLight n (applyMove n ⟨Direction.z, xTarget, yTarget⟩ cfg) xTarget yTarget zTarget =
                      ((getLight n cfg xTarget yTarget zTarget) + 1) % 2 := by
                  exact getLight_applyMoveZ_same_any n cfg hwf xTarget yTarget zTarget hx hy hz
                have hwf' : WellFormed n (applyMove n ⟨Direction.z, xTarget, yTarget⟩ cfg) :=
                  applyMove_preserves_WellFormed n ⟨Direction.z, xTarget, yTarget⟩ cfg hwf
                have htail :
                    getLight n
                      (List.foldl (fun cfg vLine =>
                        if getLight n cfg xTarget vLine 0 = 1 then
                          applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
                        else cfg)
                        (applyMove n ⟨Direction.z, xTarget, yTarget⟩ cfg) l)
                      xTarget yTarget zTarget =
                    getLight n (applyMove n ⟨Direction.z, xTarget, yTarget⟩ cfg) xTarget yTarget zTarget :=
                  other_v_preserves_cell l _ hwf' (by
                    intro vLine hvMem
                    intro hvEq
                    exact hnotmem vLine hvMem hvEq.symm)
                simp [hlit]
                rw [htail, hstep]
              · have htail :
                    getLight n
                      (List.foldl (fun cfg vLine =>
                        if getLight n cfg xTarget vLine 0 = 1 then
                          applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
                        else cfg) cfg l)
                      xTarget yTarget zTarget =
                    getLight n cfg xTarget yTarget zTarget :=
                  other_v_preserves_cell l _ hwf (by
                    intro vLine hvMem
                    intro hvEq
                    exact hnotmem vLine hvMem hvEq.symm)
                simp [hlit]
                rw [htail]
                have hfrontVal : getLight n cfg xTarget yTarget 0 = 0 := by
                  have h0 : 0 < n := by omega
                  have hfront : getLight n cfg xTarget yTarget 0 < 2 := by
                    simpa [getLight, hx, hy, h0] using hwf.2.2.2 xTarget yTarget 0 hx hy h0
                  omega
                rw [hfrontVal]
                have hcell : getLight n cfg xTarget yTarget zTarget < 2 := by
                  simpa [getLight, hx, hy, hz] using hwf.2.2.2 xTarget yTarget zTarget hx hy hz
                omega
            · by_cases hlit : getLight n cfg xTarget vLine 0 = 1
              · have hcfgTarget :
                    getLight n (applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg) xTarget yTarget zTarget =
                      getLight n cfg xTarget yTarget zTarget := by
                  exact getLight_applyMoveZ_diff_any n cfg hwf xTarget vLine xTarget yTarget zTarget (Or.inr hEq)
                have hcfgFront :
                    getLight n (applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg) xTarget yTarget 0 =
                      getLight n cfg xTarget yTarget 0 := by
                  exact getLight_applyMoveZ_diff n cfg hwf xTarget vLine xTarget yTarget hx hy (Or.inr hEq)
                have hwf' : WellFormed n (applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg) :=
                  applyMove_preserves_WellFormed n ⟨Direction.z, xTarget, vLine⟩ cfg hwf
                have hmemTail : yTarget ∈ l := by
                  cases hmem with
                  | inl h => exact False.elim (hEq h.symm)
                  | inr h => exact h
                simp [hlit]
                rw [ih _ hwf' hnodupTail hmemTail, hcfgTarget, hcfgFront]
              · have hmemTail : yTarget ∈ l := by
                  cases hmem with
                  | inl h => exact False.elim (hEq h.symm)
                  | inr h => exact h
                simp [hlit]
                exact ih _ hwf hnodupTail hmemTail
  have hmem : yTarget ∈ List.range n := by
    simpa using hy
  exact updates_mem (List.range n) config wf List.nodup_range hmem

theorem processZSurface_other_preserves_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (_hx : xTarget < n) :
    ∀ l, (∀ uLine, uLine ∈ l → uLine ≠ xTarget) →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine vLine 0 = 1 then
              applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
            else cfg) cfg)
          config l)
        xTarget yTarget zTarget =
      getLight n config xTarget yTarget zTarget := by
  intro l
  induction l generalizing config with
  | nil =>
      intro _
      rfl
  | cons uLine l ih =>
      intro hneq
      simp only [List.foldl_cons]
      have huLineNe : uLine ≠ xTarget := hneq uLine (by simp)
      have hcell :
          getLight n
            ((List.range n).foldl (fun cfg vLine =>
              if getLight n cfg uLine vLine 0 = 1 then
                applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
              else cfg) config)
            xTarget yTarget zTarget =
          getLight n config xTarget yTarget zTarget :=
        processZRow_other_preserves_cell n config wf uLine xTarget yTarget zTarget huLineNe
      have hwf' : WellFormed n
          ((List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine vLine 0 = 1 then
              applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
            else cfg) config) :=
        processZRow_preserves_WellFormed_aux n config wf uLine
      rw [ih _ hwf' (by
        intro u huMem
        exact hneq u (by simp [huMem])), hcell]

theorem processZSurface_updates_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (xTarget yTarget zTarget : Nat)
    (hx : xTarget < n) (hy : yTarget < n) (hz : zTarget < n) :
    getLight n (processZSurface n config) xTarget yTarget zTarget =
      (getLight n config xTarget yTarget zTarget + getLight n config xTarget yTarget 0) % 2 := by
  have updates_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → xTarget ∈ l →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine vLine 0 = 1 then
              applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
            else cfg) cfg)
          cfg l)
        xTarget yTarget zTarget =
      (getLight n cfg xTarget yTarget zTarget + getLight n cfg xTarget yTarget 0) % 2 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons uLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : uLine = xTarget
            · subst uLine
              have hrow :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg xTarget vLine 0 = 1 then
                        applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget =
                  (getLight n cfg xTarget yTarget zTarget + getLight n cfg xTarget yTarget 0) % 2 :=
                processZRow_same_updates_cell n cfg hwf xTarget yTarget zTarget hx hy hz
              have hwf' : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg xTarget vLine 0 = 1 then
                      applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
                    else cfg) cfg) :=
                processZRow_preserves_WellFormed_aux n cfg hwf xTarget
              have htail :
                  getLight n
                    (List.foldl (fun cfg uLine =>
                      (List.range n).foldl (fun cfg vLine =>
                        if getLight n cfg uLine vLine 0 = 1 then
                          applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
                        else cfg) cfg)
                      ((List.range n).foldl (fun cfg vLine =>
                        if getLight n cfg xTarget vLine 0 = 1 then
                          applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
                        else cfg) cfg) l)
                    xTarget yTarget zTarget =
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg xTarget vLine 0 = 1 then
                        applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget :=
                processZSurface_other_preserves_cell n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg xTarget vLine 0 = 1 then
                      applyMove n ⟨Direction.z, xTarget, vLine⟩ cfg
                    else cfg) cfg)
                  hwf' xTarget yTarget zTarget hx l
                  (by
                    intro u huMem
                    intro huEq
                    exact hnotmem u huMem huEq.symm)
              exact htail.trans hrow
            · have hcell :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg uLine vLine 0 = 1 then
                        applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget zTarget =
                  getLight n cfg xTarget yTarget zTarget :=
                processZRow_other_preserves_cell n cfg hwf uLine xTarget yTarget zTarget hEq
              have hfront :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg uLine vLine 0 = 1 then
                        applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
                      else cfg) cfg)
                    xTarget yTarget 0 =
                  getLight n cfg xTarget yTarget 0 :=
                processZRow_other_preserves_cell n cfg hwf uLine xTarget yTarget 0 hEq
              have hwf' : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg uLine vLine 0 = 1 then
                      applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
                    else cfg) cfg) :=
                processZRow_preserves_WellFormed_aux n cfg hwf uLine
              have hmemTail : xTarget ∈ l := by
                cases hmem with
                | inl h => exact False.elim (hEq h.symm)
                | inr h => exact h
              rw [ih _ hwf' hnodupTail hmemTail, hcell, hfront]
  have hmem : xTarget ∈ List.range n := by
    simpa using hx
  simpa [processZSurface, processSurface] using updates_mem (List.range n) config wf List.nodup_range hmem

theorem processYRow_other_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) (hne : uLine ≠ uTarget) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uLine 0 vLine = 1 then
          applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
        else cfg) config)
      uTarget 0 vTarget =
    getLight n config uTarget 0 vTarget := by
  induction List.range n generalizing config with
  | nil =>
      rfl
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config uLine 0 vLine = 1
      · have hcfg :
          getLight n (applyMove n ⟨Direction.y, uLine, vLine⟩ config) uTarget 0 vTarget =
            getLight n config uTarget 0 vTarget := by
          exact getLight_applyMoveY_diff n config wf uLine vLine uTarget vTarget hu hv (Or.inl hne)
        have hwf' : WellFormed n (applyMove n ⟨Direction.y, uLine, vLine⟩ config) :=
          applyMove_preserves_WellFormed n ⟨Direction.y, uLine, vLine⟩ config wf
        simp [hlit]
        rw [ih _ hwf', hcfg]
      · simp [hlit]
        rw [ih _ wf]

theorem processYRow_same_clears_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uTarget 0 vLine = 1 then
          applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg
        else cfg) config)
      uTarget 0 vTarget = 0 := by
  have zero_stays : ∀ l cfg, WellFormed n cfg →
      getLight n cfg uTarget 0 vTarget = 0 →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg uTarget 0 vLine = 1 then
            applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg
          else cfg) cfg l)
        uTarget 0 vTarget = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ hzero
        simpa using hzero
    | cons vLine l ih =>
        intro cfg hwf hzero
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg uTarget 0 vLine = 1
        · by_cases hEq : vLine = vTarget
          · subst vLine
            rw [hzero] at hlit
            cases hlit
          · have hwf' : WellFormed n (applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.y, uTarget, vLine⟩ cfg hwf
            have hzero' :
                getLight n (applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg) uTarget 0 vTarget = 0 := by
              rw [getLight_applyMoveY_diff n cfg hwf uTarget vLine uTarget vTarget hu hv (Or.inr hEq)]
              exact hzero
            simp [hlit]
            exact ih _ hwf' hzero'
        · simp [hlit]
          exact ih _ hwf hzero
  have clears_mem : ∀ l cfg, WellFormed n cfg → vTarget ∈ l →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg uTarget 0 vLine = 1 then
            applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg
          else cfg) cfg l)
        uTarget 0 vTarget = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ hmem
        cases hmem
    | cons vLine l ih =>
        intro cfg hwf hmem
        simp at hmem
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg uTarget 0 vLine = 1
        · by_cases hEq : vLine = vTarget
          · subst vLine
            have hwf' : WellFormed n (applyMove n ⟨Direction.y, uTarget, vTarget⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.y, uTarget, vTarget⟩ cfg hwf
            have hzero :
                getLight n (applyMove n ⟨Direction.y, uTarget, vTarget⟩ cfg) uTarget 0 vTarget = 0 := by
              rw [getLight_applyMoveY_same n cfg hwf uTarget vTarget hu hv]
              omega
            simp [hlit]
            exact zero_stays l _ hwf' hzero
          · have hwf' : WellFormed n (applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.y, uTarget, vLine⟩ cfg hwf
            simp [hlit]
            exact ih _ hwf' (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h)
        · by_cases hEq : vLine = vTarget
          · subst vLine
            have hzero : getLight n cfg uTarget 0 vTarget = 0 := by
              have h0 : 0 < n := by omega
              have hlt : getLight n cfg uTarget 0 vTarget < 2 := by
                simpa [getLight, hu, h0, hv] using hwf.2.2.2 uTarget 0 vTarget hu h0 hv
              omega
            simp [hlit]
            exact zero_stays l _ hwf hzero
          · simp [hlit]
            exact ih _ hwf (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h)
  have hvMem : vTarget ∈ List.range n := by
    simpa using hv
  exact clears_mem (List.range n) config wf hvMem

theorem processYRow_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine : Nat) :
    WellFormed n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uLine 0 vLine = 1 then
          applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
        else cfg) config) := by
  induction List.range n generalizing config with
  | nil =>
      simpa using wf
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config uLine 0 vLine = 1
      · simp [hlit]
        apply ih
        exact applyMove_preserves_WellFormed n ⟨Direction.y, uLine, vLine⟩ config wf
      · simp [hlit]
        exact ih _ wf

theorem processYSurface_other_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    ∀ l, (∀ uLine, uLine ∈ l → uLine ≠ uTarget) →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine 0 vLine = 1 then
              applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
            else cfg) cfg)
          config l)
        uTarget 0 vTarget =
      getLight n config uTarget 0 vTarget := by
  intro l
  induction l generalizing config with
  | nil =>
      intro _
      rfl
  | cons uLine l ih =>
      intro hneq
      simp only [List.foldl_cons]
      have huLineNe : uLine ≠ uTarget := hneq uLine (by simp)
      have hfront :
          getLight n
            ((List.range n).foldl (fun cfg vLine =>
              if getLight n cfg uLine 0 vLine = 1 then
                applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
              else cfg) config)
            uTarget 0 vTarget =
          getLight n config uTarget 0 vTarget :=
        processYRow_other_preserves_front n config wf uLine uTarget vTarget hu hv huLineNe
      have hwf' : WellFormed n
          ((List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine 0 vLine = 1 then
              applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
            else cfg) config) :=
        processYRow_preserves_WellFormed n config wf uLine
      rw [ih _ hwf' (by
        intro u huMem
        exact hneq u (by simp [huMem])), hfront]

theorem processYSurface_clears_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    getLight n (processYSurface n config) uTarget 0 vTarget = 0 := by
  have clears_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → uTarget ∈ l →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine 0 vLine = 1 then
              applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
            else cfg) cfg)
          cfg l)
        uTarget 0 vTarget = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons uLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : uLine = uTarget
            · subst uLine
              have hwfRow : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg uTarget 0 vLine = 1 then
                      applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg
                    else cfg) cfg) :=
                processYRow_preserves_WellFormed n cfg hwf uTarget
              have hclear :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg uTarget 0 vLine = 1 then
                        applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg
                      else cfg) cfg)
                    uTarget 0 vTarget = 0 :=
                processYRow_same_clears_front n cfg hwf uTarget vTarget hu hv
              have hpres := processYSurface_other_preserves_front n
                ((List.range n).foldl (fun cfg vLine =>
                  if getLight n cfg uTarget 0 vLine = 1 then
                    applyMove n ⟨Direction.y, uTarget, vLine⟩ cfg
                  else cfg) cfg)
                hwfRow uTarget vTarget hu hv l
                (by
                  intro u huMem
                  intro huEq
                  exact hnotmem u huMem huEq.symm)
              rw [hpres, hclear]
            · have hwfRow : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg uLine 0 vLine = 1 then
                      applyMove n ⟨Direction.y, uLine, vLine⟩ cfg
                    else cfg) cfg) :=
                processYRow_preserves_WellFormed n cfg hwf uLine
              have hmemTail : uTarget ∈ l := by
                cases hmem with
                | inl h => exact False.elim (hEq h.symm)
                | inr h => exact h
              simpa using ih _ hwfRow hnodupTail hmemTail
  have huMem : uTarget ∈ List.range n := by
    simpa using hu
  simpa [processYSurface, processSurface] using clears_mem (List.range n) config wf List.nodup_range huMem

theorem processSurface_clears_y_face (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v : Nat) (hu : u < n) (hv : v < n) :
    getLight n (processSurface n Direction.y config) u 0 v = 0 := by
  simpa [processYSurface] using processYSurface_clears_front n config wf u v hu hv

theorem processZRow_other_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) (hne : uLine ≠ uTarget) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uLine vLine 0 = 1 then
          applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
        else cfg) config)
      uTarget vTarget 0 =
    getLight n config uTarget vTarget 0 := by
  induction List.range n generalizing config with
  | nil =>
      rfl
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config uLine vLine 0 = 1
      · have hcfg :
          getLight n (applyMove n ⟨Direction.z, uLine, vLine⟩ config) uTarget vTarget 0 =
            getLight n config uTarget vTarget 0 := by
          exact getLight_applyMoveZ_diff n config wf uLine vLine uTarget vTarget hu hv (Or.inl hne)
        have hwf' : WellFormed n (applyMove n ⟨Direction.z, uLine, vLine⟩ config) :=
          applyMove_preserves_WellFormed n ⟨Direction.z, uLine, vLine⟩ config wf
        simp [hlit]
        rw [ih _ hwf', hcfg]
      · simp [hlit]
        rw [ih _ wf]

theorem processZRow_same_clears_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    getLight n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uTarget vLine 0 = 1 then
          applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg
        else cfg) config)
      uTarget vTarget 0 = 0 := by
  have zero_stays : ∀ l cfg, WellFormed n cfg →
      getLight n cfg uTarget vTarget 0 = 0 →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg uTarget vLine 0 = 1 then
            applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg
          else cfg) cfg l)
        uTarget vTarget 0 = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ hzero
        simpa using hzero
    | cons vLine l ih =>
        intro cfg hwf hzero
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg uTarget vLine 0 = 1
        · by_cases hEq : vLine = vTarget
          · subst vLine
            rw [hzero] at hlit
            cases hlit
          · have hwf' : WellFormed n (applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.z, uTarget, vLine⟩ cfg hwf
            have hzero' :
                getLight n (applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg) uTarget vTarget 0 = 0 := by
              rw [getLight_applyMoveZ_diff n cfg hwf uTarget vLine uTarget vTarget hu hv (Or.inr hEq)]
              exact hzero
            simp [hlit]
            exact ih _ hwf' hzero'
        · simp [hlit]
          exact ih _ hwf hzero
  have clears_mem : ∀ l cfg, WellFormed n cfg → vTarget ∈ l →
      getLight n
        (List.foldl (fun cfg vLine =>
          if getLight n cfg uTarget vLine 0 = 1 then
            applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg
          else cfg) cfg l)
        uTarget vTarget 0 = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ hmem
        cases hmem
    | cons vLine l ih =>
        intro cfg hwf hmem
        simp at hmem
        simp only [List.foldl_cons]
        by_cases hlit : getLight n cfg uTarget vLine 0 = 1
        · by_cases hEq : vLine = vTarget
          · subst vLine
            have hwf' : WellFormed n (applyMove n ⟨Direction.z, uTarget, vTarget⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.z, uTarget, vTarget⟩ cfg hwf
            have hzero :
                getLight n (applyMove n ⟨Direction.z, uTarget, vTarget⟩ cfg) uTarget vTarget 0 = 0 := by
              rw [getLight_applyMoveZ_same n cfg hwf uTarget vTarget hu hv]
              omega
            simp [hlit]
            exact zero_stays l _ hwf' hzero
          · have hwf' : WellFormed n (applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg) :=
              applyMove_preserves_WellFormed n ⟨Direction.z, uTarget, vLine⟩ cfg hwf
            simp [hlit]
            exact ih _ hwf' (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h)
        · by_cases hEq : vLine = vTarget
          · subst vLine
            have hzero : getLight n cfg uTarget vTarget 0 = 0 := by
              have h0 : 0 < n := by omega
              have hlt : getLight n cfg uTarget vTarget 0 < 2 := by
                simpa [getLight, hu, hv, h0] using hwf.2.2.2 uTarget vTarget 0 hu hv h0
              omega
            simp [hlit]
            exact zero_stays l _ hwf hzero
          · simp [hlit]
            exact ih _ hwf (by cases hmem with | inl h => exact False.elim (hEq h.symm) | inr h => exact h)
  have hvMem : vTarget ∈ List.range n := by
    simpa using hv
  exact clears_mem (List.range n) config wf hvMem

theorem processZRow_preserves_WellFormed (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uLine : Nat) :
    WellFormed n
      ((List.range n).foldl (fun cfg vLine =>
        if getLight n cfg uLine vLine 0 = 1 then
          applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
        else cfg) config) := by
  induction List.range n generalizing config with
  | nil =>
      simpa using wf
  | cons vLine l ih =>
      simp only [List.foldl_cons]
      by_cases hlit : getLight n config uLine vLine 0 = 1
      · simp [hlit]
        apply ih
        exact applyMove_preserves_WellFormed n ⟨Direction.z, uLine, vLine⟩ config wf
      · simp [hlit]
        exact ih _ wf

theorem processZSurface_other_preserves_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    ∀ l, (∀ uLine, uLine ∈ l → uLine ≠ uTarget) →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine vLine 0 = 1 then
              applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
            else cfg) cfg)
          config l)
        uTarget vTarget 0 =
      getLight n config uTarget vTarget 0 := by
  intro l
  induction l generalizing config with
  | nil =>
      intro _
      rfl
  | cons uLine l ih =>
      intro hneq
      simp only [List.foldl_cons]
      have huLineNe : uLine ≠ uTarget := hneq uLine (by simp)
      have hfront :
          getLight n
            ((List.range n).foldl (fun cfg vLine =>
              if getLight n cfg uLine vLine 0 = 1 then
                applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
              else cfg) config)
            uTarget vTarget 0 =
          getLight n config uTarget vTarget 0 :=
        processZRow_other_preserves_front n config wf uLine uTarget vTarget hu hv huLineNe
      have hwf' : WellFormed n
          ((List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine vLine 0 = 1 then
              applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
            else cfg) config) :=
        processZRow_preserves_WellFormed n config wf uLine
      rw [ih _ hwf' (by
        intro u huMem
        exact hneq u (by simp [huMem])), hfront]

theorem processZSurface_clears_front (n : Nat) (config : Config n)
    (wf : WellFormed n config) (uTarget vTarget : Nat)
    (hu : uTarget < n) (hv : vTarget < n) :
    getLight n (processZSurface n config) uTarget vTarget 0 = 0 := by
  have clears_mem : ∀ l cfg, WellFormed n cfg → List.Nodup l → uTarget ∈ l →
      getLight n
        (List.foldl (fun cfg uLine =>
          (List.range n).foldl (fun cfg vLine =>
            if getLight n cfg uLine vLine 0 = 1 then
              applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
            else cfg) cfg)
          cfg l)
        uTarget vTarget 0 = 0 := by
    intro l
    induction l with
    | nil =>
        intro cfg _ _ hmem
        cases hmem
    | cons uLine l ih =>
        intro cfg hwf hnodup hmem
        cases hnodup with
        | cons hnotmem hnodupTail =>
            simp at hmem
            simp only [List.foldl_cons]
            by_cases hEq : uLine = uTarget
            · subst uLine
              have hwfRow : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg uTarget vLine 0 = 1 then
                      applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg
                    else cfg) cfg) :=
                processZRow_preserves_WellFormed n cfg hwf uTarget
              have hclear :
                  getLight n
                    ((List.range n).foldl (fun cfg vLine =>
                      if getLight n cfg uTarget vLine 0 = 1 then
                        applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg
                      else cfg) cfg)
                    uTarget vTarget 0 = 0 :=
                processZRow_same_clears_front n cfg hwf uTarget vTarget hu hv
              have hpres := processZSurface_other_preserves_front n
                ((List.range n).foldl (fun cfg vLine =>
                  if getLight n cfg uTarget vLine 0 = 1 then
                    applyMove n ⟨Direction.z, uTarget, vLine⟩ cfg
                  else cfg) cfg)
                hwfRow uTarget vTarget hu hv l
                (by
                  intro u huMem
                  intro huEq
                  exact hnotmem u huMem huEq.symm)
              rw [hpres, hclear]
            · have hwfRow : WellFormed n
                  ((List.range n).foldl (fun cfg vLine =>
                    if getLight n cfg uLine vLine 0 = 1 then
                      applyMove n ⟨Direction.z, uLine, vLine⟩ cfg
                    else cfg) cfg) :=
                processZRow_preserves_WellFormed n cfg hwf uLine
              have hmemTail : uTarget ∈ l := by
                cases hmem with
                | inl h => exact False.elim (hEq h.symm)
                | inr h => exact h
              simpa using ih _ hwfRow hnodupTail hmemTail
  have huMem : uTarget ∈ List.range n := by
    simpa using hu
  simpa [processZSurface, processSurface] using clears_mem (List.range n) config wf List.nodup_range huMem

theorem processSurface_clears_z_face (n : Nat) (config : Config n)
    (wf : WellFormed n config) (u v : Nat) (hu : u < n) (hv : v < n) :
    getLight n (processSurface n Direction.z config) u v 0 = 0 := by
  simpa [processZSurface] using processZSurface_clears_front n config wf u v hu hv

-- Progress note (GPT-5.4, 2026-04-07): this also needs `WellFormed`.
-- On raw `Config`, a front-face entry can be `2`, in which case the algorithm does
-- not press that square and the conclusion is false.
theorem processSurface_clears_face (n : Nat) (dir : Direction) (config : Config n)
  (wf : WellFormed n config)
    (u v : Nat) (hu : u < n) (hv : v < n) :
    let result := processSurface n dir config
    match dir with
    | Direction.x => getLight n result 0 u v = 0
    | Direction.y => getLight n result u 0 v = 0
    | Direction.z => getLight n result u v 0 = 0 := by
  cases dir
  · simpa using processSurface_clears_x_face n config wf u v hu hv
  · simpa using processSurface_clears_y_face n config wf u v hu hv
  · simpa using processSurface_clears_z_face n config wf u v hu hv

-- Warning (GPT-5.4, 2026-04-07): the three preservation statements below are false.
-- They are replaced by explicit counterexamples so the proof frontier matches the
-- actual behavior of the algorithm.

def counterexampleSurfaceCfg : Config 2 :=
  [[[1, 0], [0, 0]], [[0, 0], [0, 0]]]

theorem processYSurface_preserves_xface_counterexample :
    getLight 2 counterexampleSurfaceCfg 0 1 0 = 0 ∧
    getLight 2 (processYSurface 2 counterexampleSurfaceCfg) 0 1 0 = 1 := by
  native_decide

theorem processZSurface_preserves_xface_counterexample :
    getLight 2 counterexampleSurfaceCfg 0 0 1 = 0 ∧
    getLight 2 (processZSurface 2 counterexampleSurfaceCfg) 0 0 1 = 1 := by
  native_decide

theorem processZSurface_preserves_yface_counterexample :
    getLight 2 counterexampleSurfaceCfg 0 0 1 = 0 ∧
    getLight 2 (processZSurface 2 counterexampleSurfaceCfg) 0 0 1 = 1 := by
  native_decide

-- Progress note (GPT-5.4, 2026-04-07):
-- The forward direction below is proved. The reverse direction appears to need
-- a well-formedness hypothesis, because `IsAllOff` only quantifies over indices
-- `< n`, while `isAllOff` inspects the entire nested list structure.
theorem isAllOff_implies_IsAllOff (n : Nat) (config : Config n) :
    isAllOff n config = true → IsAllOff n config := by
  intro hAll x y z hx hy hz
  simp [getLight, hx, hy, hz]
  have hLayer :
      (fun layer => layer.all fun row => row.all fun light => decide (light = 0)) (listGet config x []) = true := by
    apply listGet_all_eq_true (p := fun layer => layer.all fun row => row.all fun light => decide (light = 0)) config x []
    · simpa [isAllOff] using hAll
    · simp
  have hRow :
      (fun row => row.all fun light => decide (light = 0)) (listGet (listGet config x []) y []) = true := by
    apply listGet_all_eq_true (p := fun row => row.all fun light => decide (light = 0)) (listGet config x []) y []
    · exact hLayer
    · simp
  have hLight : (fun light => decide (light = 0)) (listGet (listGet (listGet config x []) y []) z 0) = true := by
    apply listGet_all_eq_true (p := fun light => decide (light = 0)) (listGet (listGet config x []) y []) z 0
    · exact hRow
    · simp
  simpa using hLight

theorem IsAllOff_implies_isAllOff (n : Nat) (config : Config n)
    (wf : WellFormed n config) :
    IsAllOff n config → isAllOff n config = true := by
  intro hOff
  rw [isAllOff]
  apply List.all_eq_true.mpr
  intro layer hLayerMem
  apply List.all_eq_true.mpr
  intro row hRowMem
  apply List.all_eq_true.mpr
  intro light hLightMem
  rcases List.mem_iff_get.mp hLayerMem with ⟨ix, hix⟩
  rcases List.mem_iff_get.mp hRowMem with ⟨iy, hiy⟩
  rcases List.mem_iff_get.mp hLightMem with ⟨iz, hiz⟩
  let x := ix.1
  let y := iy.1
  let z := iz.1
  have hxLen : x < config.length := by
    exact ix.2
  have hx : x < n := by
    simpa [wf.1] using hxLen
  have hLayerEq : listGet config x [] = layer := by
    rw [listGet_eq_get config x [] hxLen]
    simpa [x] using hix
  have hyLen : y < (listGet config x []).length := by
    rw [hLayerEq]
    exact iy.2
  have hy : y < n := by
    simpa [wf.2.1 x hx] using hyLen
  have hRowEq : listGet (listGet config x []) y [] = row := by
    rw [listGet_eq_get (listGet config x []) y [] hyLen]
    simpa [y, hLayerEq] using hiy
  have hzLen : z < (listGet (listGet config x []) y []).length := by
    rw [hRowEq]
    exact iz.2
  have hz : z < n := by
    simpa [wf.2.2.1 x y hx hy] using hzLen
  have hGetZero : listGet (listGet (listGet config x []) y []) z 0 = 0 := by
    simpa [getLight, hx, hy, hz] using hOff x y z hx hy hz
  have hLightEq : listGet (listGet (listGet config x []) y []) z 0 = light := by
    rw [listGet_eq_get (listGet (listGet config x []) y []) z 0 hzLen]
    simpa [z, hRowEq] using hiz
  have hLightZero : light = 0 := by
    calc
      light = listGet (listGet (listGet config x []) y []) z 0 := by symm; exact hLightEq
      _ = 0 := hGetZero
  simpa using hLightZero

-- Bool and Prop versions agree
theorem isAllOff_iff_IsAllOff (n : Nat) (config : Config n)
    (wf : WellFormed n config) :
    isAllOff n config = true ↔ IsAllOff n config := by
  constructor
  · exact isAllOff_implies_IsAllOff n config
  · exact IsAllOff_implies_isAllOff n config wf

theorem ValidConfig.isAllOff_iff_IsAllOff {n : Nat} (config : ValidConfig n) :
    config.isAllOff = true ↔ config.IsAllOff := by
  exact _root_.LightPuzzle.isAllOff_iff_IsAllOff n config.data config.wf

theorem ValidConfig.applyMove_comm {n : Nat} (config : ValidConfig n) (m1 m2 : Move n) :
    LightPuzzle.applyMove n m1 (LightPuzzle.applyMove n m2 config.data) =
    LightPuzzle.applyMove n m2 (LightPuzzle.applyMove n m1 config.data) := by
  exact _root_.LightPuzzle.applyMove_comm n m1 m2 config.data config.wf

-- Progress note (GPT-5.4, 2026-04-07): the two raw theorems below are false.
-- The correct final statement must restrict to legal binary states, e.g. via
-- `WellFormed` or `ValidConfig`. The counterexample is the in-bounds non-binary
-- state `[[[2]]]`: it is solvable, but the greedy algorithm does nothing because
-- it only presses when the inspected light is exactly `1`.

def greedyRawCounterexample : Config 1 := [[[2]]]

theorem greedyAlgorithm_correct_counterexample :
    IsSolvable 1 greedyRawCounterexample ∧
    ¬ IsAllOff 1 (greedyAlgorithm 1 greedyRawCounterexample) := by
  constructor
  · refine ⟨[⟨Direction.x, 0, 0⟩, ⟨Direction.x, 0, 0⟩], ?_⟩
    intro x y z hx hy hz
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    have hz0 : z = 0 := by omega
    subst x
    subst y
    subst z
    native_decide
  · intro hall
    have hzero : getLight 1 (greedyAlgorithm 1 greedyRawCounterexample) 0 0 0 = 0 := by
      exact hall 0 0 0 (by omega) (by omega) (by omega)
    have htwo : getLight 1 (greedyAlgorithm 1 greedyRawCounterexample) 0 0 0 = 2 := by
      native_decide
    omega

theorem solvability_characterization_counterexample :
    ¬ (IsSolvable 1 greedyRawCounterexample ↔ IsAllOff 1 (greedyAlgorithm 1 greedyRawCounterexample)) := by
  intro hiff
  have hsolv : IsSolvable 1 greedyRawCounterexample := greedyAlgorithm_correct_counterexample.1
  have hnot : ¬ IsAllOff 1 (greedyAlgorithm 1 greedyRawCounterexample) :=
    greedyAlgorithm_correct_counterexample.2
  exact hnot (hiff.mp hsolv)

-- Corrected final theorems: these are the intended statements for legal binary
-- puzzle states. The unrestricted raw versions above are false, but the theorem
-- names below are restored in the `WellFormed` setting.

instance instDecidableForallFin {n : Nat} {P : Fin n → Prop} [∀ i, Decidable (P i)] :
  Decidable (∀ i, P i) := by
  induction n with
  | zero =>
    exact isTrue (by intro i; exact Fin.elim0 i)
  | succ n ih =>
    let Ptail : Fin n → Prop := fun i => P i.succ
    have h0 : Decidable (P 0) := inferInstance
    have htail : Decidable (∀ i : Fin n, Ptail i) := ih
    cases h0 with
    | isTrue hp0 =>
      cases htail with
      | isTrue hsucc =>
        exact isTrue (by
        intro i
        rcases i with ⟨i, hi⟩
        cases i with
        | zero => simpa using hp0
        | succ i =>
          exact hsucc ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
      | isFalse hsucc =>
        exact isFalse (by
        intro hall
        apply hsucc
        intro i
        exact hall i.succ)
    | isFalse hp0 =>
      exact isFalse (by
      intro hall
      exact hp0 (hall 0))

theorem greedyAlgorithm_bit_formula_fin
    (a b c d e f g h : Fin 2) :
    ((((a.1 + b.1) % 2 + (c.1 + e.1) % 2) % 2 +
        (((d.1 + f.1) % 2 + (g.1 + h.1) % 2) % 2)) % 2) =
      (a.1 + b.1 + c.1 + d.1 + e.1 + f.1 + g.1 + h.1) % 2 := by
  native_decide +revert

private def witnessParityCancel_fin_check
    (a b c d e f g h : Fin 2)
    (pxyz pyxz pzxy py0z pz0y px0z pxy0 pyx0 pzx0 pz00 py00 px00 : Fin 2) : Bool :=
  decide (
    (a.1 + pxyz.1 + pyxz.1 + pzxy.1) % 2 = 0 →
    (b.1 + pxyz.1 + py0z.1 + pz0y.1) % 2 = 0 →
    (c.1 + px0z.1 + pyxz.1 + pzx0.1) % 2 = 0 →
    (d.1 + pxy0.1 + pyx0.1 + pzxy.1) % 2 = 0 →
    (e.1 + px0z.1 + py0z.1 + pz00.1) % 2 = 0 →
    (f.1 + pxy0.1 + py00.1 + pz0y.1) % 2 = 0 →
    (g.1 + px00.1 + pyx0.1 + pzx0.1) % 2 = 0 →
    (h.1 + px00.1 + py00.1 + pz00.1) % 2 = 0 →
    (a.1 + b.1 + c.1 + d.1 + e.1 + f.1 + g.1 + h.1) % 2 = 0)

theorem witnessParityCancel_fin_check_true :
    ∀ a b c d e f g h : Fin 2,
    ∀ pxyz pyxz pzxy py0z pz0y px0z pxy0 pyx0 pzx0 pz00 py00 px00 : Fin 2,
      witnessParityCancel_fin_check
        a b c d e f g h
        pxyz pyxz pzxy py0z pz0y px0z pxy0 pyx0 pzx0 pz00 py00 px00 = true := by
  native_decide

theorem witnessParityCancel_fin
    (a b c d e f g h : Fin 2)
    (pxyz pyxz pzxy py0z pz0y px0z pxy0 pyx0 pzx0 pz00 py00 px00 : Fin 2)
    (h1 : (a.1 + pxyz.1 + pyxz.1 + pzxy.1) % 2 = 0)
    (h2 : (b.1 + pxyz.1 + py0z.1 + pz0y.1) % 2 = 0)
    (h3 : (c.1 + px0z.1 + pyxz.1 + pzx0.1) % 2 = 0)
    (h4 : (d.1 + pxy0.1 + pyx0.1 + pzxy.1) % 2 = 0)
    (h5 : (e.1 + px0z.1 + py0z.1 + pz00.1) % 2 = 0)
    (h6 : (f.1 + pxy0.1 + py00.1 + pz0y.1) % 2 = 0)
    (h7 : (g.1 + px00.1 + pyx0.1 + pzx0.1) % 2 = 0)
    (h8 : (h.1 + px00.1 + py00.1 + pz00.1) % 2 = 0) :
    (a.1 + b.1 + c.1 + d.1 + e.1 + f.1 + g.1 + h.1) % 2 = 0 := by
  have hcheck := witnessParityCancel_fin_check_true
    a b c d e f g h
    pxyz pyxz pzxy py0z pz0y px0z pxy0 pyx0 pzx0 pz00 py00 px00
  have hor :
      (a.1 + pxyz.1 + pyxz.1 + pzxy.1) % 2 = 1 ∨
      (b.1 + pxyz.1 + py0z.1 + pz0y.1) % 2 = 1 ∨
      (c.1 + px0z.1 + pyxz.1 + pzx0.1) % 2 = 1 ∨
      (d.1 + pxy0.1 + pyx0.1 + pzxy.1) % 2 = 1 ∨
      (e.1 + px0z.1 + py0z.1 + pz00.1) % 2 = 1 ∨
      (f.1 + pxy0.1 + py00.1 + pz0y.1) % 2 = 1 ∨
      (g.1 + px00.1 + pyx0.1 + pzx0.1) % 2 = 1 ∨
      (h.1 + px00.1 + py00.1 + pz00.1) % 2 = 1 ∨
      (a.1 + b.1 + c.1 + d.1 + e.1 + f.1 + g.1 + h.1) % 2 = 0 := by
    simpa [witnessParityCancel_fin_check] using hcheck
  simpa [h1, h2, h3, h4, h5, h6, h7, h8] using hor

theorem greedyAlgorithm_updates_cell (n : Nat) (config : Config n)
    (wf : WellFormed n config) (x y z : Nat)
    (hx : x < n) (hy : y < n) (hz : z < n) :
    getLight n (greedyAlgorithm n config) x y z =
      (getLight n config x y z +
        getLight n config 0 y z +
        getLight n config x 0 z +
        getLight n config x y 0 +
        getLight n config 0 0 z +
        getLight n config 0 y 0 +
        getLight n config x 0 0 +
        getLight n config 0 0 0) % 2 := by
  have h0 : 0 < n := by omega
  have wfX : WellFormed n (processXSurface n config) :=
    processXSurface_preserves_WellFormed n config wf
  have wfXY : WellFormed n (processYSurface n (processXSurface n config)) :=
    processYSurface_preserves_WellFormed n (processXSurface n config) wfX
  have hX_xyz := processXSurface_updates_cell n config wf x y z hx hy hz
  have hX_x0z := processXSurface_updates_cell n config wf x 0 z hx h0 hz
  have hX_xy0 := processXSurface_updates_cell n config wf x y 0 hx hy h0
  have hX_x00 := processXSurface_updates_cell n config wf x 0 0 hx h0 h0
  have hY_xyz := processYSurface_updates_cell n (processXSurface n config) wfX x y z hx hy hz
  have hY_xy0 := processYSurface_updates_cell n (processXSurface n config) wfX x y 0 hx hy h0
  unfold greedyAlgorithm
  rw [processZSurface_updates_cell n (processYSurface n (processXSurface n config)) wfXY x y z hx hy hz]
  rw [hY_xyz, hY_xy0, hX_xyz, hX_x0z, hX_xy0, hX_x00]
  have hxyz : getLight n config x y z < 2 := by
    simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
  have h0yz : getLight n config 0 y z < 2 := by
    simpa [getLight, h0, hy, hz] using wf.2.2.2 0 y z h0 hy hz
  have hx0z : getLight n config x 0 z < 2 := by
    simpa [getLight, hx, h0, hz] using wf.2.2.2 x 0 z hx h0 hz
  have hxy0 : getLight n config x y 0 < 2 := by
    simpa [getLight, hx, hy, h0] using wf.2.2.2 x y 0 hx hy h0
  have h00z : getLight n config 0 0 z < 2 := by
    simpa [getLight, h0, h0, hz] using wf.2.2.2 0 0 z h0 h0 hz
  have h0y0 : getLight n config 0 y 0 < 2 := by
    simpa [getLight, h0, hy, h0] using wf.2.2.2 0 y 0 h0 hy h0
  have hx00 : getLight n config x 0 0 < 2 := by
    simpa [getLight, hx, h0, h0] using wf.2.2.2 x 0 0 hx h0 h0
  have h000 : getLight n config 0 0 0 < 2 := by
    simpa [getLight, h0, h0, h0] using wf.2.2.2 0 0 0 h0 h0 h0
  let a : Fin 2 := ⟨getLight n config x y z, hxyz⟩
  let b : Fin 2 := ⟨getLight n config 0 y z, h0yz⟩
  let c : Fin 2 := ⟨getLight n config x 0 z, hx0z⟩
  let d : Fin 2 := ⟨getLight n config x y 0, hxy0⟩
  let e : Fin 2 := ⟨getLight n config 0 0 z, h00z⟩
  let f : Fin 2 := ⟨getLight n config 0 y 0, h0y0⟩
  let g : Fin 2 := ⟨getLight n config x 0 0, hx00⟩
  let hbit : Fin 2 := ⟨getLight n config 0 0 0, h000⟩
  have hflat := greedyAlgorithm_bit_formula_fin a b c d e f g hbit
  simpa [a, b, c, d, e, f, g, hbit] using hflat

theorem greedyAlgorithm_correct (n : Nat) (config : Config n)
    (wf : WellFormed n config) (h : IsSolvable n config) :
    IsAllOff n (greedyAlgorithm n config) := by
  rcases h with ⟨moves, hOff⟩
  intro x y z hx hy hz
  have h0 : 0 < n := by omega
  have hgreedy := greedyAlgorithm_updates_cell n config wf x y z hx hy hz
  rw [hgreedy]
  have hxyz :
      (getLight n config x y z + xParity moves y z + yParity moves x z + zParity moves x y) % 2 = 0 := by
    calc
      (getLight n config x y z + xParity moves y z + yParity moves x z + zParity moves x y) % 2
        = getLight n (applyMoves n moves config) x y z := by
            symm
            exact getLight_applyMoves_formula n config wf moves x y z hx hy hz
      _ = 0 := hOff x y z hx hy hz
  have h0yz :
      (getLight n config 0 y z + xParity moves y z + yParity moves 0 z + zParity moves 0 y) % 2 = 0 := by
    calc
      (getLight n config 0 y z + xParity moves y z + yParity moves 0 z + zParity moves 0 y) % 2
        = getLight n (applyMoves n moves config) 0 y z := by
            symm
            exact getLight_applyMoves_formula n config wf moves 0 y z h0 hy hz
      _ = 0 := hOff 0 y z h0 hy hz
  have hx0zEq :
      (getLight n config x 0 z + xParity moves 0 z + yParity moves x z + zParity moves x 0) % 2 = 0 := by
    calc
      (getLight n config x 0 z + xParity moves 0 z + yParity moves x z + zParity moves x 0) % 2
        = getLight n (applyMoves n moves config) x 0 z := by
            symm
            exact getLight_applyMoves_formula n config wf moves x 0 z hx h0 hz
      _ = 0 := hOff x 0 z hx h0 hz
  have hxy0Eq :
      (getLight n config x y 0 + xParity moves y 0 + yParity moves x 0 + zParity moves x y) % 2 = 0 := by
    calc
      (getLight n config x y 0 + xParity moves y 0 + yParity moves x 0 + zParity moves x y) % 2
        = getLight n (applyMoves n moves config) x y 0 := by
            symm
            exact getLight_applyMoves_formula n config wf moves x y 0 hx hy h0
      _ = 0 := hOff x y 0 hx hy h0
  have h00zEq :
      (getLight n config 0 0 z + xParity moves 0 z + yParity moves 0 z + zParity moves 0 0) % 2 = 0 := by
    calc
      (getLight n config 0 0 z + xParity moves 0 z + yParity moves 0 z + zParity moves 0 0) % 2
        = getLight n (applyMoves n moves config) 0 0 z := by
            symm
            exact getLight_applyMoves_formula n config wf moves 0 0 z h0 h0 hz
      _ = 0 := hOff 0 0 z h0 h0 hz
  have h0y0Eq :
      (getLight n config 0 y 0 + xParity moves y 0 + yParity moves 0 0 + zParity moves 0 y) % 2 = 0 := by
    calc
      (getLight n config 0 y 0 + xParity moves y 0 + yParity moves 0 0 + zParity moves 0 y) % 2
        = getLight n (applyMoves n moves config) 0 y 0 := by
            symm
            exact getLight_applyMoves_formula n config wf moves 0 y 0 h0 hy h0
      _ = 0 := hOff 0 y 0 h0 hy h0
  have hx00Eq :
      (getLight n config x 0 0 + xParity moves 0 0 + yParity moves x 0 + zParity moves x 0) % 2 = 0 := by
    calc
      (getLight n config x 0 0 + xParity moves 0 0 + yParity moves x 0 + zParity moves x 0) % 2
        = getLight n (applyMoves n moves config) x 0 0 := by
            symm
            exact getLight_applyMoves_formula n config wf moves x 0 0 hx h0 h0
      _ = 0 := hOff x 0 0 hx h0 h0
  have h000Eq :
      (getLight n config 0 0 0 + xParity moves 0 0 + yParity moves 0 0 + zParity moves 0 0) % 2 = 0 := by
    calc
      (getLight n config 0 0 0 + xParity moves 0 0 + yParity moves 0 0 + zParity moves 0 0) % 2
        = getLight n (applyMoves n moves config) 0 0 0 := by
            symm
            exact getLight_applyMoves_formula n config wf moves 0 0 0 h0 h0 h0
      _ = 0 := hOff 0 0 0 h0 h0 h0
  have pxyz : xParity moves y z < 2 := moveParity_lt_two (xMove y z) moves
  have px0z : xParity moves 0 z < 2 := moveParity_lt_two (xMove 0 z) moves
  have pxy0 : xParity moves y 0 < 2 := moveParity_lt_two (xMove y 0) moves
  have px00 : xParity moves 0 0 < 2 := moveParity_lt_two (xMove 0 0) moves
  have pyxz : yParity moves x z < 2 := moveParity_lt_two (yMove x z) moves
  have py0z : yParity moves 0 z < 2 := moveParity_lt_two (yMove 0 z) moves
  have pyx0 : yParity moves x 0 < 2 := moveParity_lt_two (yMove x 0) moves
  have py00 : yParity moves 0 0 < 2 := moveParity_lt_two (yMove 0 0) moves
  have pzxy : zParity moves x y < 2 := moveParity_lt_two (zMove x y) moves
  have pz0y : zParity moves 0 y < 2 := moveParity_lt_two (zMove 0 y) moves
  have pzx0 : zParity moves x 0 < 2 := moveParity_lt_two (zMove x 0) moves
  have pz00 : zParity moves 0 0 < 2 := moveParity_lt_two (zMove 0 0) moves
  have cxyz : getLight n config x y z < 2 := by
    simpa [getLight, hx, hy, hz] using wf.2.2.2 x y z hx hy hz
  have c0yz : getLight n config 0 y z < 2 := by
    simpa [getLight, h0, hy, hz] using wf.2.2.2 0 y z h0 hy hz
  have cx0z : getLight n config x 0 z < 2 := by
    simpa [getLight, hx, h0, hz] using wf.2.2.2 x 0 z hx h0 hz
  have cxy0 : getLight n config x y 0 < 2 := by
    simpa [getLight, hx, hy, h0] using wf.2.2.2 x y 0 hx hy h0
  have c00z : getLight n config 0 0 z < 2 := by
    simpa [getLight, h0, h0, hz] using wf.2.2.2 0 0 z h0 h0 hz
  have c0y0 : getLight n config 0 y 0 < 2 := by
    simpa [getLight, h0, hy, h0] using wf.2.2.2 0 y 0 h0 hy h0
  have cx00 : getLight n config x 0 0 < 2 := by
    simpa [getLight, hx, h0, h0] using wf.2.2.2 x 0 0 hx h0 h0
  have c000 : getLight n config 0 0 0 < 2 := by
    simpa [getLight, h0, h0, h0] using wf.2.2.2 0 0 0 h0 h0 h0
  let a : Fin 2 := ⟨getLight n config x y z, cxyz⟩
  let b : Fin 2 := ⟨getLight n config 0 y z, c0yz⟩
  let c : Fin 2 := ⟨getLight n config x 0 z, cx0z⟩
  let d : Fin 2 := ⟨getLight n config x y 0, cxy0⟩
  let e : Fin 2 := ⟨getLight n config 0 0 z, c00z⟩
  let f : Fin 2 := ⟨getLight n config 0 y 0, c0y0⟩
  let g : Fin 2 := ⟨getLight n config x 0 0, cx00⟩
  let hbit : Fin 2 := ⟨getLight n config 0 0 0, c000⟩
  let pxyzF : Fin 2 := ⟨xParity moves y z, pxyz⟩
  let pyxzF : Fin 2 := ⟨yParity moves x z, pyxz⟩
  let pzxyF : Fin 2 := ⟨zParity moves x y, pzxy⟩
  let py0zF : Fin 2 := ⟨yParity moves 0 z, py0z⟩
  let pz0yF : Fin 2 := ⟨zParity moves 0 y, pz0y⟩
  let px0zF : Fin 2 := ⟨xParity moves 0 z, px0z⟩
  let pxy0F : Fin 2 := ⟨xParity moves y 0, pxy0⟩
  let pyx0F : Fin 2 := ⟨yParity moves x 0, pyx0⟩
  let pzx0F : Fin 2 := ⟨zParity moves x 0, pzx0⟩
  let pz00F : Fin 2 := ⟨zParity moves 0 0, pz00⟩
  let py00F : Fin 2 := ⟨yParity moves 0 0, py00⟩
  let px00F : Fin 2 := ⟨xParity moves 0 0, px00⟩
  have hcancel := witnessParityCancel_fin
    a b c d e f g hbit
    pxyzF pyxzF pzxyF py0zF pz0yF px0zF pxy0F pyx0F pzx0F pz00F py00F px00F
    (by simpa [a, pxyzF, pyxzF, pzxyF] using hxyz)
    (by simpa [b, pxyzF, py0zF, pz0yF] using h0yz)
    (by simpa [c, px0zF, pyxzF, pzx0F] using hx0zEq)
    (by simpa [d, pxy0F, pyx0F, pzxyF] using hxy0Eq)
    (by simpa [e, px0zF, py0zF, pz00F] using h00zEq)
    (by simpa [f, pxy0F, py00F, pz0yF] using h0y0Eq)
    (by simpa [g, px00F, pyx0F, pzx0F] using hx00Eq)
    (by simpa [hbit, px00F, py00F, pz00F] using h000Eq)
  simpa [a, b, c, d, e, f, g, hbit] using hcancel

theorem solvability_characterization (n : Nat) (config : Config n)
    (wf : WellFormed n config) :
    IsSolvable n config ↔ IsAllOff n (greedyAlgorithm n config) := by
  constructor
  · exact greedyAlgorithm_correct n config wf
  · intro hgreedy
    refine ⟨(greedyAlgorithmTrace n config).2, ?_⟩
    rw [greedyAlgorithmTrace_sound, greedyAlgorithmTrace_fst]
    exact hgreedy

/-! ## Tracing the Greedy Algorithm -/

def traceGreedy (n : Nat) (config : Config n) : String :=
  let step0 := config
  let msg0 := "=== Initial configuration ===\n" ++ prettyPrint n step0

  let step1 := processXSurface n step0
  let msg1 := "\n\n=== After processXSurface ===\n" ++ prettyPrint n step1

  let step2 := processYSurface n step1
  let msg2 := "\n\n=== After processYSurface ===\n" ++ prettyPrint n step2

  let step3 := processZSurface n step2
  let msg3 := "\n\n=== After processZSurface ===\n" ++ prettyPrint n step3

  let result := "\n\n=== Result: " ++
    (if isAllOff n step3 then "ALL OFF ✓" else "NOT all off ✗") ++ " ==="

  msg0 ++ msg1 ++ msg2 ++ msg3 ++ result

#eval IO.println (traceGreedy 3 configExample1)
#eval IO.println (traceGreedy 3 configExample2)

end LightPuzzle
