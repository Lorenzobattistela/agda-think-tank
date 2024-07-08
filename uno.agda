module uno where 

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _+_; _<_; _<?_; _*_)
open import Data.Nat.Properties
open import Data.Nat.DivMod 
open import Function using (_∘_)
open import Data.Fin using (Fin; toℕ; fromℕ<; fromℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; _∨_; _∧_; if_then_else_)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty

data Color : Set where
  Red Green Blue Yellow : Color

-- define equality for colors
_colorEq_ : Color → Color → Bool
Red colorEq Red = true
Green colorEq Green = true
Blue colorEq Blue = true
Yellow colorEq Yellow = true
_ colorEq _ = false

Card : Set
Card = Color × ℕ

Player : Set
Player = List Card

Deck : Set
Deck = List Card

sameColor : Card → Card → Bool
sameColor (c₁ , _) (c₂ , _) = c₁ colorEq c₂

sameNumber : Card → Card → Bool
sameNumber (_ , n₁) (_ , n₂) = (n₁) ≡ᵇ (n₂) 

canPlay : Card → Card → Bool
canPlay card₁ card₂ = sameColor card₁ card₂ ∨ sameNumber card₁ card₂

cardEqual : Card → Card → Bool
cardEqual card₁ card₂ = sameColor card₁ card₂ ∧ sameNumber card₁ card₂

-- in the recursive case, if c cardEqual card, return cs. If not, return c ∷ removeCard cs card
removeCard : Player → Card → Player
removeCard [] _ = []
removeCard (c ∷ cs) card = if cardEqual c card then cs else c ∷ removeCard cs card

c : Card
c = Red , 5

d : Card
d = Blue , 1

p : Player
p = (Red , 5) ∷ (Blue , 7) ∷ []

_ : removeCard p c ≡ (Blue , 7) ∷ []
_ = refl

-- receives a player, the card on the table and return a decidable play
pickCard : Player → Card → Maybe Card
pickCard [] _ = nothing 
pickCard (c ∷ cs) topCard =
  if canPlay c topCard
  then just c
  else pickCard cs topCard



_ : pickCard p d ≡ just (Blue , 7)
_ = refl

_ : pickCard p (Yellow , 9) ≡ nothing
_ = refl

-- receive length of players, current player and return the next one
-- if we have 0 players, return 0
-- if the player is 1 - length, return 0
nextPlayer : ℕ → ℕ → ℕ
nextPlayer zero _ = zero
nextPlayer (suc n) m with m <? n
... | yes _ = suc m
... | no _ = 0

nextPlayerLessLength : nextPlayer 3 1 ≡ 2
nextPlayerLessLength = refl
nextPlayerWraps : nextPlayer 3 2 ≡ 0
nextPlayerWraps = refl

playerWin : Player → Bool
playerWin [] = true
playerWin (c ∷ cs) = false

-- same purpose of the above but receives length
playerWin′ : ℕ → Bool
playerWin′ zero = true
playerWin′ _ = false


pseudoRandom : ℕ → ℕ → ℕ
pseudoRandom seed limit = ((1664525 * seed) + 1013904223) % limit

-- fill in the generateColor function. It calls pseudoRandom with the seed received and limit 4, and matches.
-- If 0, pick red, if 1 pick blue, if 2 picks green, if 3 picks yellow. 
generateColor : ℕ → Color
generateColor seed with pseudoRandom seed 4
... | 0 = Red
... | 1 = Blue
... | 2 = Green
... | 3 = Yellow
... | _ = Red

generateNumber : ℕ → ℕ
generateNumber seed = pseudoRandom seed 9

generateCard : ℕ → Card
generateCard seed = ((generateColor seed) , (generateNumber seed))

-- receives num of cards, seed
generatePlayer : ℕ →  ℕ → Player
generatePlayer zero seed = []
generatePlayer (suc n) seed = (generateCard seed) ∷ (generatePlayer n seed) 

getPlayer : ℕ → List Player → Player
getPlayer zero (c ∷ cs) = c
getPlayer zero [] = []
getPlayer (suc n) (c ∷ cs) = getPlayer n cs
getPlayer (suc n) [] = []

record GameState : Set where
  field
    numPlayers : ℕ
    players : List Player
    currentPlayer : ℕ
    topCard : Card
    turnsWithNoPlay : ℕ

data Result : Set where
  Tie : ℕ → ℕ → Result
  P1_Won : Result
  P2_Won : Result
  
-- receives currentPLayer, topCard and turnsWithNoPlay
updateGameState : GameState → ℕ → Card → ℕ → GameState
updateGameState gs current top turnsIdle = 
  let
    n = GameState.numPlayers gs
    ps = GameState.players gs
  in
    record
    { numPlayers = n
    ; players = ps
    ; currentPlayer = current
    ; topCard = top
    ; turnsWithNoPlay = turnsIdle
    }

-- receives the picked card and the table card, returns the new card on the table
playCard : Maybe Card → Card → Card
playCard nothing tableCard = tableCard
playCard (just card) _ = card


-- receives oldTopCard, newTop, oldIdle and returns newIdle
calculateIdle : Card → Card → ℕ → ℕ
calculateIdle c₁ c₂ n = if cardEqual c₁ c₂ then suc (n) else n

play : GameState → Result
play gs =
  let
    n = GameState.numPlayers gs
    current = GameState.currentPlayer gs
    top = GameState.topCard gs
    idleTurns = GameState.turnsWithNoPlay gs
    players = GameState.players gs

    p1 = getPlayer 0 players
    cards_p1 = length p1
    p1_won = playerWin′ cards_p1

    p2 = getPlayer 1 players
    cards_p2 = length p2
    p2_won = playerWin′ cards_p2

    currentPlayer = getPlayer current players
    toPlayCard = pickCard currentPlayer top
    nextP = nextPlayer n current

    nextTop = playCard toPlayCard top
    nextIdle = calculateIdle top nextTop idleTurns
  in
    if idleTurns ≥ᵇ 2
    then Tie cards_p1 cards_p2
    else if current ≡ᵇ 0
         then (if p1_won
               then P1_Won
               else play ( ( updateGameState gs nextP nextTop nextIdle ) ) )
         else if p2_won
               then P2_Won
               else P2_Won






