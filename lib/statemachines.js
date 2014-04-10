if (typeof module === "object")
	module.exports = StateMachine;

if (typeof require === "function") {
	var SortedArray = require("sorted-array");
	require("augment");
}

var sortable = Function.bindable(SortedArray, null);

function StateMachine(transition, final) {
	this.transition = transition;
	this.final = final;
}

StateMachine.Deterministic = StateMachine.augment(function (base) {
		this.constructor = function (transition, final) {
			base.constructor.call(this, transition, final);
		};

		this.test = function (string) {
			var state = 0,
			index = 0;
			var length = string.length;
			var transition = this.transition;
			while (index < length) {
				state = transition[state][string.charAt(index++)];
				if (typeof state === "undefined")
					return false;
			}

			return this.final.indexOf(state) >= 0;
		};

		this.alphabet = function (){
			var alphabet = new SortedArray();
			for (var i = 0;i < this.transition.length; i++)
			{
				for (var symbol in this.transition[i])
				{
					if (alphabet.search(symbol) < 0)
					{
						alphabet.insert(symbol);
					}
				}
			}

			return alphabet;
		};

		this.minimize = function (){
			// Minimize with the Hopcroft Algorithm
			// http://en.wikipedia.org/wiki/DFA_minimization#Hopcroft.27s_algorithm

			var states = set();
			var i=0;
			for (var state in this.transition)
			{
				states = set(states,i);
				i++;
			}
			
			var FinalSet = set();
			for (var i = 0;i < this.final.length ;i++)
			{
				FinalSet = set(FinalSet, this.final[i]);
			}

			// Find alphabet
			var alphabet = this.alphabet();

			/// Hopcroft
			var P = new Array(set.difference(states, FinalSet) , FinalSet);
			var W = new Array(FinalSet);
			
			while(W.length > 0)
			{
				var A = W.pop();
				
				// For each in alphabet
				for (var j = 0 ; j < alphabet.array.length ;j++)
				{
					var c = alphabet.array[j];
					
					var X = set();
					for (var k = 0;k < this.transition.length; k++)
					{
						var check = this.transition[k][c];
						if ( set.contains(A, check ))
						{
							X = set(X, k);
						}
					}
					
					if (set.count(X) > 0)
					{
						// We have found a X
						for (var k = 0;k < P.length; k++)
						{
							var Y = P[k];
							var intersect = set.intersection(X, Y);
							var diff = set.difference(Y, X);
							
							if ( set.count(intersect) > 0 && set.count(diff) >0)
							{
								P.splice(k,1, intersect, diff); 
								
								// Search if Y is in W
								var found = false;
								for (var kk = 0;kk < W.length ; kk++)
								{
									if (set.equals(W[kk], Y))
									{
										W.splice(kk,1, intersect, diff);
										found = true;
										break;
									}
								}
								
								if (!found)
								{
									if (set.count(intersect) <= set.count(diff))
									{
										W.push(intersect);
									}
									else
									{
										W.push(diff);
									}
								}
							}
						}
					}
				}
			}
			
			P.sort(function (a , b) {  return parseInt(Object.keys(a)[0]) -  parseInt(Object.keys(b)[0]) });
			var newTransitions = [];
			var newFinals = [];
			for (var i = 0; i < P.length; i++)
			{
				var stateinP = Object.keys(P[i])[0];
				var newTrans = {};
				
				for (var symbol in this.transition[stateinP])
				{
					var oldState = this.transition[stateinP][symbol];
					for (var j = 0; j < P.length; j++)
					{
						if (set.contains(P[j], oldState))
						{
							newTrans[symbol] = j;
							break;
						}
					}
				}
				newTransitions.push(newTrans);
				
				if (this.final.indexOf(parseInt(stateinP)) > -1)
				{
					newFinals.push(i);
				}
			}
			
			var newDFA = new StateMachine.Deterministic(newTransitions, newFinals);
			return newDFA;

		};	
	});

StateMachine.Nondeterministic = StateMachine.augment(function (base) {
		this.constructor = function (transition, final) {
			base.constructor.call(this, transition, final);
		};

		this.test = function (string) {
			var index = 0;
			var length = string.length;
			var state = epsilonMoves.call(this, 0);
			while (index < length) {
				state = moveOn.apply(this, [string.charAt(index++)].concat(state));
				if (state.length)
					state = epsilonMoves.apply(this, state);
				else
					return false;
			}

			return isFinal.apply(this, state);
		};

		this.subset = function () {
			var initial = epsilonMoves.call(this, 0);
			var names = [initial.toString()];
			var states = [initial];
			var transition = [];
			var final = [];

			for (var i = 0; i < states.length; i++) {
				var state = states[i];
				var symbols = moves.apply(this, state);
				var length = symbols.length;
				var node = {};

				for (var j = 0; j < length; j++) {
					var symbol = symbols[j];
					var next = epsilonMoves.apply(this,
							moveOn.apply(this, [symbol].concat(state)));
					var name = next.toString();
					var index = names.indexOf(name);

					if (index < 0) {
						states.push(next);
						index = names.length;
						names.push(name);
					}

					node[symbol] = index;
				}

				transition.push(node);

				if (isFinal.apply(this, state))
					final.push(i);
			}

			return new StateMachine.Deterministic(transition, final);
		};

		this.subsetEpsilon = function () {
			var transition = [];
			var eClosures = [];
			
			for (var i = 0; i < this.transition.length; i++) {
				eClosures[i] = epsilonMoves.call(this, i);
			}
		
			for (var i = 0; i < this.transition.length; i++) {
				var node = {};
				var symbols = moves.apply(this, eClosures[i]);

				for (var j = 0; j < symbols.length; j++) {

					var next = moveOn.apply(this, [symbols[j]].concat(eClosures[i]));
					
					// now we take the Eclosure of every next

					var curTransition = new SortedArray;

					if (next.length) {
						for (var k = 0; k < next.length; k++) {
							var thisStates = eClosures[next[k]];
							
							for (var l =0; l < thisStates.length;l++) {
								if (curTransition.search(thisStates[l]) < 0) {
									curTransition.insert(thisStates[l]);
								}
							}
						}
					}

					node[symbols[j]] = curTransition.array;
				}

				transition.push(node);

			}
	
			return new StateMachine.Nondeterministic(transition, this.final);
		};

		function epsilonMoves() {
			var stack = Array.from(arguments);
			var states = new(sortable.apply(null, stack));
			var transition = this.transition;
			while (stack.length) {
				var moves = transition[stack.pop()][""];

				if (moves) {
					var length = moves.length;

					for (var i = 0; i < length; i++) {
						var move = moves[i];

						if (states.search(move) < 0) {
							states.insert(move);
							stack.push(move);
						}
					}
				}
			}

			return states.array;
		}

		function moves() {
			var transition = this.transition;
			var stack = Array.from(arguments);
			var symbols = new SortedArray;
			while (stack.length) {
				var keys = Object.keys(transition[stack.pop()]);
				var length = keys.length;

				for (var i = 0; i < length; i++) {
					var key = keys[i];

					if (symbols.search(key) < 0)
						symbols.insert(key);
				}
			}

			return symbols.remove("").array;
		}

		function moveOn(symbol) {
			var stack = Array.from(arguments, 1);
			var transition = this.transition;
			var states = new SortedArray;
			while (stack.length) {
				var moves = transition[stack.pop()][symbol];

				if (moves) {
					var length = moves.length;

					for (var i = 0; i < length; i++) {
						var move = moves[i];

						if (states.search(move) < 0)
							states.insert(move);
					}
				}
			}

			return states.array;
		}

		function isFinal() {
			var stack = Array.from(arguments);
			var final = this.final;
			while (stack.length)
				if (final.indexOf(stack.pop()) >= 0)
					return true;

			return false;
		}
	});
