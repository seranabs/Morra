'reach 0.1';

// create enum for first 5 fingers
//const [ isHand, ZERO, ONE, TWO, THREE, FOUR, FIVE ] = makeEnum(6);

// create enum for results
const [ isResult, NO_WINS, A_WINS, B_WINS, DRAW,  ] = makeEnum(4);

// 0 = none, 1 = B wins, 2 = draw , 3 = A wins
const winner = (handAether, guessAether, handLumine, guessLumine) => {
  const total = handAether + handLumine;

  if ( guessAether == total && guessLumine == total  ) {
      // draw
      return DRAW
  }  else if ( guessLumine == total) {
      // Lumine wins
      return B_WINS
  }
  else if ( guessAether == total ) { 
      // Aether wins
      return A_WINS
  } else {
    // else noone wins
      return NO_WINS
  }
 
}
  
assert(winner(1,2,1,3 ) == A_WINS);
assert(winner(5,10,5,8 ) == A_WINS);

assert(winner(3,6,4,7 ) == B_WINS);
assert(winner(1,5,3,4 ) == B_WINS);

assert(winner(0,0,0,0 ) == DRAW);
assert(winner(2,4,2,4 ) == DRAW);
assert(winner(5,10,5,10 ) == DRAW);

assert(winner(3,6,2,4 ) == NO_WINS);
assert(winner(0,3,1,5 ) == NO_WINS);

forall(UInt, handAether =>
  forall(UInt, handLumine =>
    forall(UInt, guessAether =>
      forall(UInt, guessLumine =>
    assert(isResult(winner(handAether, guessAether, handLumine , guessLumine)))
))));


// Setup common functions
const commonInteract = {
  ...hasRandom,
  reportResult: Fun([UInt], Null),
  reportHands: Fun([UInt, UInt, UInt, UInt], Null),
  informTimeout: Fun([], Null),
  getHand: Fun([], UInt),
  getGuess: Fun([], UInt),
};

const AetherInterect = {
  ...commonInteract,
  wager: UInt, 
  deadline: UInt, 
}

const LumineInteract = {
  ...commonInteract,
  acceptWager: Fun([UInt], Null),
}


export const main = Reach.App(() => {
  const A = Participant('Aether',AetherInterect );
  const B = Participant('Lumine', LumineInteract );
  init();

  // Check for timeouts
  const informTimeout = () => {
    each([A, B], () => {
      interact.informTimeout();
    });
  };

  A.only(() => {
    const wager = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  });
  A.publish(wager, deadline)
    .pay(wager);
  commit();

  B.only(() => {
    interact.acceptWager(wager);
  });
  B.pay(wager)
    .timeout(relativeTime(deadline), () => closeTo(A, informTimeout));
  

  var result = DRAW;
   invariant( balance() == 2 * wager && isResult(result) );

   ///////////////// While DRAW or NO_WINS //////////////////////////////
   while ( result == DRAW || result == NO_WINS ) {
    commit();

  A.only(() => {
    const _handAether = interact.getHand();
    const [_commitAether1, _saltAether1] = makeCommitment(interact, _handAether);
    const commitAether1 = declassify(_commitAether1);

    const _guessAether = interact.getGuess();
    const [_commitAether2, _saltAether2] = makeCommitment(interact, _guessAether);
    const commitAether2 = declassify(_commitAether2);

  })
  

  A.publish(commitAether1, commitAether2)
      .timeout(relativeTime(deadline), () => closeTo(B, informTimeout));
    commit();

  // Lumine must NOT know about Aether hand and guess
  unknowable(B, A(_handAether,_guessAether, _saltAether1,_saltAether2 ));
  
  // Get Lumine  hand
  B.only(() => {
    const handLumine = declassify(interact.getHand());
    const guessLumine = declassify(interact.getGuess());
  });

  B.publish(handLumine, guessLumine)
    .timeout(relativeTime(deadline), () => closeTo(A, informTimeout));
  commit();

  A.only(() => {
    const saltAether1 = declassify(_saltAether1);
    const handAether = declassify(_handAether);
    const saltAether2 = declassify(_saltAether2);
    const guessAether = declassify(_guessAether);

  });

  A.publish(saltAether1,saltAether2, handAether, guessAether)
    .timeout(relativeTime(deadline), () => closeTo(B, informTimeout));
  checkCommitment(commitAether1, saltAether1, handAether);
  checkCommitment(commitAether2, saltAether2, guessAether);

  
  each([A, B], () => {
    interact.reportHands(handAether, guessAether, handLumine, guessLumine);
  });

  result = winner(handAether, guessAether, handLumine, guessLumine);
  continue;
}
// check to make sure no DRAW or NO_WINS
assert(result == A_WINS || result == B_WINS);

each([A, B], () => {
  interact.reportResult(result);
});

transfer(2 * wager).to(result == A_WINS ? A : B);
commit();

});
