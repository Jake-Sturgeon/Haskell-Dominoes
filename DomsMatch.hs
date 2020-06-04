module DomsMatch where

 {- play a 5's & 3's singles match between 2 given players
    play n games, each game up to 61
 -} 

 --import Doms
 import System.Random
 import Data.List
 import Debug.Trace
 import Data.Maybe
 
 type Tactic = Hand -> DomBoard -> Player -> Scores -> Maybe Move

 {-| 
   The bestPlayer function returns a Move 
    It uses the play54, get61, block61, get59, and block59 tactics
    Otherwise use hsdPlayer
   It takes one arguments of type: DomsPlayer
 -}
 bestPlayer :: DomsPlayer
 bestPlayer hnd InitBoard p s
   | isJust start = fromJust start
   where start = play54 hnd InitBoard p s
 bestPlayer hnd brd p s
   | itsScore > 52 && isJust canWin = fromJust canWin
   | oScore > 52 && isJust canBlock61 = fromJust canBlock61
   | itsScore > 50 && isJust can59 = fromJust can59
   | oScore > 50 && isJust canBlock59 = fromJust canBlock59
   | otherwise = hsdPlayer hnd brd p s
   where
        canWin = get61 hnd brd p s
        can59 = get59 hnd brd p s
        canBlock61 = block61 hnd brd p s
        canBlock59 = block59 hnd brd p s
        scr = getScore s
        itsScore = scr p
        oScore = scr (swapP p)


 {-| 
   The player54canWinBlockGet59 function returns a Move 
    It uses the play54, get61, block61, and get59 tactics
    Otherwise use hsdPlayer
   It takes one arguments of type: DomsPlayer
 -}
 player54canWinBlockGet59 :: DomsPlayer
 player54canWinBlockGet59 hnd InitBoard p s
   | isJust start = fromJust start
   where start = play54 hnd InitBoard p s
 player54canWinBlockGet59 hnd brd p s
   | itsScore > 52 && isJust canWin = fromJust canWin
   | oScore > 52 && isJust canBlock61 = fromJust canBlock61
   | itsScore > 50 && isJust can59 = fromJust can59
   | otherwise = hsdPlayer hnd brd p s
   where 
        canWin = get61 hnd brd p s
        can59 = get59 hnd brd p s
        canBlock61 = block61 hnd brd p s
        scr = getScore s
        itsScore = scr p
        oScore = scr (swapP p)


 {-| 
   The player54canWinBlock function returns a Move 
    It uses the play54, get61, and block61 tactics
    Otherwise use hsdPlayer
   It takes one arguments of type: DomsPlayer
 -}
 player54canWinBlock :: DomsPlayer
 player54canWinBlock hnd InitBoard p s
   | isJust start = fromJust start
   where start = play54 hnd InitBoard p s
 player54canWinBlock hnd brd p s 
   | itsScore > 52 && isJust canWin = fromJust canWin
   | oScore > 52 && isJust canBlock = fromJust canBlock
   | otherwise = hsdPlayer hnd brd p s
   where 
        canWin = get61 hnd brd p s
        canBlock = block61 hnd brd p s
        scr = getScore s
        itsScore = scr p
        oScore = scr (swapP p)


 {-| 
   The player54canWin function returns a Move 
    It uses the play54, and get 61 tactics
    Otherwise use hsdPlayer
   It takes one arguments of type: DomsPlayer
 -}
 player54canWin :: DomsPlayer
 player54canWin hnd InitBoard p s
   | isJust start = fromJust start
   where start = play54 hnd InitBoard p s
 player54canWin hnd brd p s 
   | score > 52 && isJust canWin = fromJust canWin
   | otherwise = hsdPlayer hnd brd p s
   where 
        canWin = get61 hnd brd p s
        score = getScore s p


 {-| 
   The player54 function returns a Move 
    It uses the play54 tactic
    Otherwise use hsdPlayer
   It takes one arguments of type: DomsPlayer
 -}
 player54 :: DomsPlayer
 player54 hnd InitBoard p s
   | isJust start = fromJust start
   where start = play54 hnd InitBoard p s
 player54 hnd brd p s = hsdPlayer hnd brd p s


 
 {-| 
   The play54 function returns a maybe dom of (5,4)
   It takes three argument of type: History, (current) player, and Hand
 -}
 play54 :: Tactic 
 play54 [] _ _ _ = Nothing
 play54 hnd _ _ _
  | elem (5,4) hnd = Just ((5,4), L)
  | otherwise = Nothing


 {-| 
   The get61 function returns a maybe Move if the player can get the score 59
   It takes one arguments of type: Tactic
 -}
 get61 :: Tactic
 get61 t = getNum 61 t


 {-| 
   The get59 function returns a maybe Move if the player can get the score 59
   It takes one arguments of type: Tactic
 -}
 get59 :: Tactic
 get59 t = getNum 59 t


 {-| 
   The getNum function returns a maybe Move if the player can get the
    given score
   It takes two arguments of type: Int, and Tactic
 -}
 getNum :: Int -> Tactic
 getNum _ [] _ _ _ = Nothing
 getNum n hnd brd p s
   | not(null plays) = Just (head plays)
   | otherwise = Nothing
   where 
        plays = [move | ldrop <- ld, scoreDom ldrop L brd == n - scr , let move = (ldrop, L)] ++   -- construc a list of dom that can score N
                [move | rdrop <- rd, scoreDom rdrop R brd == n - scr , let move = (rdrop, R)] 
        ld = leftdrops hnd brd
        rd = rightdrops hnd brd
        scr = getScore s p                 -- get the given players score


 {-| 
   The block61 function returns a maybe Move if the player can block the
    score of 61
   It takes one arguments of type: Tactic
 -}
 block61 :: Tactic
 block61 t = blockNum 61 t
 
 {-| 
   The block59 function returns a maybe Move if the player can block the
    score of 59
   It takes one arguments of type: Tactic
 -}
 block59 :: Tactic
 block59 t = blockNum 59 t

 {-| 
   The blockNum function returns a maybe Move if the player can block the
    other players given score
   It takes one arguments of type: Int, and Tactic
 -}
 blockNum :: Int -> Tactic
 blockNum _ _ InitBoard _ _ = Nothing
 blockNum n hnd brd@(Board _ _ h) p s
   | isJust doesNum = doesNum
   | otherwise = Nothing
   where 
        guess = guessHand h p hnd
        sDom = sortDom hnd brd
        doesNum = blockNumA n sDom guess brd p s


 {-| 
   The sortDom function returns the other player given a player
   It takes one arguments of type: Player
 -}
 blockNumA :: Int -> Hand -> Hand -> DomBoard -> Player -> Scores -> Maybe Move
 blockNumA _ [] _ _ _ _ = Nothing
 blockNumA n (h:t) hnd brd p s
   | not(null lPlays) && not(isJust getLNum) = Just (h,L)           -- if you can play on the left and the player doesnt get the given score then play the dom
   | not(null rPlays) && not(isJust getRNum) = Just (h,R)           -- if you can play on the right and the player doesnt get the given score then play the dom
   | otherwise = blockNumA n t hnd brd p s                          -- Otherwise, try next dom
   where 
        lPlays = leftdrops [h] brd                                  -- List of leftplays
        rPlays = rightdrops [h] brd                                 -- List of rightplays
        oP = swapP p                                                -- The other player
        getLNum = getNum n hnd (updateBoard h L p brd) oP s         -- see if the player can score the given n on the left side of the board
        getRNum = getNum n hnd (updateBoard h R p brd) oP s         -- see if the player can score the given n on the right side of the board


 {-| 
   The sortDom function returns a list of sorted doms 
   relative to what it would score on the given board
   It takes two arguments of type: [Dom] and DomBoard
 -}
 sortDom :: [Dom] -> DomBoard -> [Dom]
 sortDom doms brd = map fst slis               -- return a list of sorted doms
  where 
        lis = map (\x -> (x, scoreDom x L brd)) lPlays ++ map (\x -> (x, scoreDom x R brd)) rPlays  -- Construct a list of pairs where the first value is the dom 
                                                                                                       -- then the score it would produce if played
        slis = sortBy (\(_,n2) (_,n1) -> compare n1 n2) lis                                         -- sort the list into descending order
        lPlays = leftdrops doms brd                                                                 -- list of left plays
        rPlays = rightdrops doms brd                                                                -- list of right plays


 {-| 
   The swapP function returns the other player given a player
   It takes one arguments of type: Player
 -}
 swapP :: Player -> Player
 swapP p
  | p == P1 = P2
  | otherwise = P1
        

 {-| 
   The getScore function returns the given players score
   It takes two arguments of type: Score, and Player
 -}
 getScore :: Scores -> Player -> Int
 getScore (l, r) p
  | p == P1 = l
  | otherwise = r


 {-| 
   The guessHand function returns a list of all the possible doms the other player may have
   It takes three argument of type: History, (current) player, and Hand

   DESCRIPTION:
    It uses the knowledge of: what its current hand is, what has been played, and what has been
    knock by the opponent to construct a 'guess' at what the hand could be

    If the History is empty, return the filtered domSet
 -}
 guessHand :: History -> Player -> Hand -> Hand
 guessHand [] _ hnd = filter (\x -> notElem x hnd) domSet
 guessHand hist plr hnd = doms                                                -- Return the knowledge
  where 
        sHist = sortBy (\(_,_,n1) (_,_,n2) -> compare n1 n2) hist             -- Sort the history into time order (ascending)
        kTimes = whenKnocked sHist plr                                        -- A list of times at which the opponent was knocking
        tBoard = getBoardAtTime hist kTimes                                   -- Get a list of histories where the opponent was knocking
        dHave = dontHave tBoard                                               -- A list of doms the opponent doesn't have due to knocks
        dHaveDoms = map (\(dom,_,_) -> dom) hist ++ hnd ++ dHave              -- Concatenate all the knowledge together 
        sDoms = map (\(l, r) -> if (l > r) then (l,r) else (r,l)) dHaveDoms   -- swap the doms to where the first spot value is the largest
        doms = filter (\x -> notElem x sDoms) domSet                          -- filter the knowledge against the domSet
 

 {-| 
   The dontHave function returns a list of all the possible doms the other player could have after taking
    their knocks into account
   It takes one argument of type: [History]

   DESCRIPTION:
    This uses the list of histories to construct a list of dominoes that opponent doesnt have by using the 
    knowledge generated about what doms have been knocked
 -}
 dontHave :: [History] -> [Dom]
 dontHave hists = [(x,y) | x <- [0..6], y <- ls]
  where ls = nub (map (\((l,_),_,_) -> l) (map head hists) ++ map (\((_,r),_,_) -> r) (map last hists))
 

 {-| 
   The getBoardAtTime function returns a list of historys at the given times
   It takes two argument of type: History and [Int]

   DESCRIPTION:
    This takes a History and a list of Ints. The list of Ints are used to filter the history down into the times
    you want. Returns a list of Histories
 -}
 getBoardAtTime :: History -> [Int] -> [History]
 getBoardAtTime _ [] = []
 getBoardAtTime hist (h:t) = (filter (\(_,_,time) -> time <= h) hist) : getBoardAtTime hist t


 {-| 
   The whenKnocked function returns a list of times where the other player was knocking
   It takes two argument of type: History (sorted in terms of times asc) and Player

   DESCRIPTION:
    It takes the sorted History and compares if two consecutive plays are by the same player
    as this implies that the other player was knocking
    There is a case where the last turn played was also a knock which is when the length of the
    list is 1 
 -}
 whenKnocked :: History -> Player -> [Int]
 whenKnocked list@((_,p,time):_) plr
   | len && p == plr = [time] 
   | len = []
   where len = (length list) == 1
 whenKnocked list@(h@(_, p1, time):t@((_, p2, _):_)) plr 
   | k = time : whenKnocked t plr
   | otherwise = whenKnocked t plr
   where k = p1 == plr && p2 == plr

 ------------- DomsMatch Code ------------------------------------------------------------------
 ------------- DomsMatch Code ------------------------------------------------------------------
 ------------- DomsMatch Code ------------------------------------------------------------------
 ------------- DomsMatch Code ------------------------------------------------------------------
 ------------- DomsMatch Code ------------------------------------------------------------------
 ------------- DomsMatch Code ------------------------------------------------------------------

 type Dom = (Int,Int)
 -- with highest pip first i.e. (6,1) not (1,6)

 data DomBoard = InitBoard|Board Dom Dom History
                    deriving (Show)
 
 type History = [(Dom,Player,MoveNum)]
 -- History allows course of game to be reconstructed                                            
                                               
 data Player = P1|P2 -- player 1 or player 2
                  deriving (Eq,Show)
 
 data End = L|R -- left end or right end
                  deriving (Eq,Show)
 
 type MoveNum = Int

 type Hand = [Dom]
  
 -- the full set of Doms
 domSet :: [Dom]
 
 domSet = [(6,6),(6,5),(6,4),(6,3),(6,2),(6,1),(6,0),
                 (5,5),(5,4),(5,3),(5,2),(5,1),(5,0),
                       (4,4),(4,3),(4,2),(4,1),(4,0),
                             (3,3),(3,2),(3,1),(3,0),
                                   (2,2),(2,1),(2,0),
                                         (1,1),(1,0),
                                               (0,0)]
                                                                                         
 
 type Move = (Dom,End)
 type Scores = (Int,Int)
                                                                                              
 -- state in a game - p1's hand, p2's hand, player to drop, current board, scores 
 type GameState =(Hand,Hand,Player, DomBoard, Scores)
 
 
 ------------------------------------------------------
 {- DomsPlayer
    given a Hand, the Board, which Player this is and the current Scores
    returns a Dom and an End
    only called when player is not knocking
    made this a type, so different players can be created
 -}
 
 type DomsPlayer = Hand->DomBoard->Player->Scores->(Dom,End)
 
 {- variables
     hand h
     board b
     player p
     scores s
 -}




 -- guessHist :: DomsPlayer
 -- guessHist h b@(InitBoard) p s = (d,e)
 --  where (d,e,_) = hsd h b
 -- guessHist h b@(Board _ _ hist) p s = traceShow (guessHand hist p h) (d,e)
 --  where (d,e,_)=hsd h b

 -- example players
 -- randomPlayer plays the first legal dom it can, even if it goes bust
 randomPlayer :: DomsPlayer
 
 randomPlayer h b p s 
  |not(null ldrops) = ((head ldrops),L)
  |otherwise = ((head rdrops),R)
  where
   ldrops = leftdrops h b
   rdrops = rightdrops h b
   
 -- hsdplayer plays highest scoring dom
 
 hsdPlayer :: DomsPlayer
 hsdPlayer h b p s = (d,e)
                     where (d,e,_)=hsd h b
                     
  -- highest scoring dom

 hsd :: Hand->DomBoard->(Dom,End,Int)
 
 hsd h InitBoard = (md,L,ms)
  where
   dscores = zip h (map (\ (d1,d2)->score53 (d1+d2)) h)
   (md,ms) = maximumBy (comparing snd) dscores
   
 
 hsd h b = 
   let
    ld=  leftdrops h b
    rd = rightdrops h b
    lscores = zip ld (map (\d->(scoreDom d L b)) ld) -- [(Dom, score)]
    rscores = zip rd (map (\d->(scoreDom d R b)) rd)
    (lb,ls) = if (not(null lscores)) then (maximumBy (comparing snd) lscores) else ((0,0),-1) -- can't be chosen
    (rb,rs) = if (not(null rscores)) then (maximumBy (comparing snd) rscores) else ((0,0),-1)
   in
    if (ls>rs) then (lb,L,ls) else (rb,R,rs)
 
 
                                               
 -----------------------------------------------------------------------------------------
 {- top level fn
    args: 2 players (p1, p2), number of games (n), random number seed (seed)
    returns: number of games won by player 1 & player 2
    calls playDomsGames giving it n, initial score in games and random no gen
 -} 
 
 domsMatch :: DomsPlayer->DomsPlayer->Int->Int->(Int,Int)
 
 domsMatch p1 p2 n seed = playDomsGames p1 p2 n (0,0) (mkStdGen seed)
 
 -----------------------------------------------------------------------------------------
 
{- playDomsGames plays n games

  p1,p2 players
  (s1,s2) their scores
  gen random generator
-}
 
 playDomsGames :: DomsPlayer->DomsPlayer->Int->(Int,Int)->StdGen->(Int,Int)
 
 playDomsGames _ _ 0 score_in_games _ = score_in_games -- stop when n games played
 
 playDomsGames p1 p2 n (s1,s2) gen 
   |gameres==P1 = playDomsGames p1 p2 (n-1) (s1+1,s2) gen2 -- p1 won
   |otherwise = playDomsGames p1 p2 (n-1) (s1,s2+1) gen2 -- p2 won
  where
   (gen1,gen2)=split gen -- get 2 generators, so doms can be reshuffled for next hand
   gameres = playDomsGame p1 p2 (if (odd n) then P1 else P2) (0,0) gen1 -- play next game p1 drops if n odd else p2
 
 -----------------------------------------------------------------------------------------
 -- playDomsGame plays a single game - 61 up
 -- returns winner - P1 or P2
 -- the Bool pdrop is true if it's p1 to drop
 -- pdrop alternates between games
 
 playDomsGame :: DomsPlayer->DomsPlayer->Player->(Int,Int)->StdGen->Player
 
 playDomsGame p1 p2 pdrop scores gen 
  |s1==61 = P1
  |s2==61 = P2
  |otherwise = playDomsGame p1 p2 (if (pdrop==P1) then P2 else P1) (s1,s2) gen2
  where
   (gen1,gen2)=split gen
   (s1,s2)=playDomsHand p1 p2 pdrop scores gen1  
  
 -----------------------------------------------------------------------------------------
 -- play a single hand
  
 playDomsHand :: DomsPlayer->DomsPlayer->Player->(Int,Int)->StdGen->(Int,Int)
 
 playDomsHand p1 p2 nextplayer scores gen = 
   playDoms p1 p2 init_gamestate
  where
   spack = shuffleDoms gen
   p1_hand = take 9 spack
   p2_hand = take 9 (drop 9 spack)
   init_gamestate = (p1_hand,p2_hand,nextplayer,InitBoard,scores) 
   
 ------------------------------------------------------------------------------------------   
 -- shuffle 
 
 shuffleDoms :: StdGen -> [Dom]

 shuffleDoms gen =  
  let
    weights = take 28 (randoms gen :: [Int])
    dset = (map fst (sortBy  
               (\ (_,w1)(_,w2)  -> (compare w1 w2)) 
               (zip domSet weights)))
  in
   dset
   
 ------------------------------------------------------------------------------------------
 -- playDoms runs the hand
 -- returns scores at the end

 
 playDoms :: DomsPlayer->DomsPlayer->GameState->(Int,Int)
 
 playDoms _ _ (_,_,_,_, (61,s2)) = (61,s2) --p1 has won the game
 playDoms _ _ (_,_,_,_, (s1,61)) = (s1,61) --p2 has won the game
 
 
 playDoms p1 p2 gs@(h1,h2,nextplayer,b,scores)
  |(kp1 &&  kp2) = scores -- both players knocking, end of the hand
  |((nextplayer==P1) && (not kp1)) = playDoms p1 p2 (p1play p1 gs) -- p1 plays, returning new gameState. p2 to go next
  |(nextplayer==P1) = playDoms p1 p2 (p2play p2 gs) -- p1 knocking so p2 plays
  |(not kp2) = playDoms p1 p2 (p2play p2 gs) -- p2 plays
  |otherwise = playDoms p1 p2 (p1play p1 gs) -- p2 knocking so p1 plays
  where
   kp1 = knocking h1 b -- true if p1 knocking
   kp2 = knocking h2 b -- true if p2 knocking
   
 ------------------------------------------------------------------------------------------
 -- is a player knocking?

 knocking :: Hand->DomBoard->Bool
 
 knocking h b = 
  ((null (leftdrops h b)) && (null (rightdrops h b))) -- leftdrops & rightdrops in doms.hs
 
 ------------------------------------------------------------------------------------------
   
 -- player p1 to drop
 
 p1play :: DomsPlayer->GameState->GameState
 
 p1play p1 (h1,h2,_,b, (s1,s2)) =
  ((delete dom h1), h2, P2,(updateBoard dom end P1 b), (ns1, s2))
   where
    (dom,end) = p1 h1 b P1 (s1,s2)-- call the player, returning dom dropped and end it's dropped at.
    score = s1+ (scoreDom dom end b) -- what it scored
    ns1 = if (score >61) then s1 else score -- check for going bust
    
 
 -- p2 to drop
   
 p2play :: DomsPlayer->GameState->GameState
 
 p2play p2 (h1,h2,_,b,(s1,s2)) =
  (h1, (delete dom h2),P1, (updateBoard dom end P2 b), (s1, ns2))
  where
   (dom,end) = p2 h2 b P2 (s1,s2)-- call the player, returning dom dropped and end it's dropped at.
   score = s2+ (scoreDom dom end b) -- what it scored
   ns2 = if (score >61) then s2 else score -- check for going bust
 
   -------------------------------------------------------------------------------------------
 -- updateBoard 
 -- update the board after a play
 
 updateBoard :: Dom->End->Player->DomBoard->DomBoard
 
 updateBoard d e p b
  -- |e==L = traceShow (playleft p d b) (playleft p d b)
  -- |otherwise = traceShow (playright p d b) (playright p d b)
  | e==L = playleft p d b
  | otherwise = playright p d b

  ------------------------------------------------------------------------------------------
 -- doms which will go left
 leftdrops :: Hand->DomBoard->Hand
 
 leftdrops h b = filter (\d -> goesLP d b) h
 
 -- doms which go right
 rightdrops :: Hand->DomBoard->Hand
 
 rightdrops h b = filter (\d -> goesRP d b) h 
 
 -------------------------------------------------
 -- 5s and 3s score for a number
  
 score53 :: Int->Int
 score53 n = 
  let 
   s3 = if (rem n 3)==0 then (quot n 3) else 0
   s5 = if (rem n 5)==0 then (quot n 5) else 0 
  in
   s3+s5
   
 ------------------------------------------------ 
 -- need comparing
 -- useful fn specifying what we want to compare by
 comparing :: Ord b=>(a->b)->a->a->Ordering
 comparing f l r = compare (f l) (f r)
 
 ------------------------------------------------
 -- scoreDom
 -- what will a given Dom score at a given end?
 -- assuming it goes
 
 scoreDom :: Dom->End->DomBoard->Int
 
 scoreDom d e b = scoreboard nb
                  where
                  (Just nb) = (playDom P1 d e b) -- player doesn't matter
 
 ----------------------------------------------------                 
 -- play to left - it will go
 playleft :: Player->Dom->DomBoard->DomBoard
 
 playleft p (d1,d2) InitBoard = Board (d1,d2) (d1,d2) [((d1,d2),p,1)]
 
 playleft p (d1,d2) (Board (l1,l2) r h)
  |d1==l1 = Board (d2,d1) r (((d2,d1),p,n+1):h)
  |otherwise =Board (d1,d2) r (((d1,d2),p,n+1):h)
  where
    n = maximum [m |(_,_,m)<-h] -- next drop number
    
 -- play to right
 playright :: Player->Dom->DomBoard->DomBoard
 
 playright p (d1,d2) InitBoard = Board (d1,d2) (d1,d2) [((d1,d2),p,1)]
 
 playright p (d1,d2)(Board l (r1,r2) h)
  |d1==r2 = Board l (d1,d2) (h++[((d1,d2),p,n+1)])
  |otherwise = Board l (d2,d1) (h++[((d2,d1),p,n+1)])
  where 
    n = maximum [m |(_,_,m)<-h] -- next drop number
 
 ------------------------------------------------------
 -- predicate - will given domino go at left?
 -- assumes a dom has been played
 
 goesLP :: Dom->DomBoard->Bool
 
 goesLP _ InitBoard = True
 
 goesLP (d1,d2) (Board (l,_) _ _) = (l==d1)||(l==d2)


 -- will dom go to the right?
 -- assumes a dom has been played
 
 goesRP :: Dom->DomBoard->Bool
 
 goesRP _ InitBoard = True
 
 goesRP (d1,d2) (Board _ (_,r) _) = (r==d1)||(r==d2)
 
 ------------------------------------------------

 -- playDom
 -- given player plays
 -- play a dom at left or right, if it will go

 
 playDom :: Player->Dom->End->DomBoard->Maybe DomBoard
 
 playDom p d L b
   |goesLP d b = Just (playleft p d b)
   |otherwise = Nothing
 
 playDom p d R b
   |goesRP d b = Just (playright p d b)
   |otherwise = Nothing
   
 ---------------------------------------------------    
 -- 5s & threes score for a board
 
 scoreboard :: DomBoard -> Int
 
 scoreboard InitBoard = 0

 scoreboard (Board (l1,l2) (r1,r2) hist)
  |length hist == 1 = score53 (l1+l2) -- 1 dom played, it's both left and right end
  |otherwise = score53 ((if l1==l2 then 2*l1 else l1)+ (if r1==r2 then 2*r2 else r2))   