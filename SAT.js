/*
 * sat.js
 * (C) 2012, all rights reserved,
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * DESCRIPTION:
 *     This is a SAT solver implemented in javascript.
 */

/*
 * State constructor.
 */
function State()
{
    this.empty = false;
    this.vars = [null];
    this.clauses = [];
    this.trail = [];
    this.dlevel = 0;
    this.tlevel = 0;
}

/*
 * Variable constructor.
 */
function Variable()
{
    this.set = false;
    this.sign = false;
    this.mark = false;
    this.unit = false;
    this.unit_sign = false;
    this.dlevel = 0;
    this.reason = null;
    this.watches = [[], []];

    this.setUnit = function(sign) {
        this.unit = true;
        this.unit_sign = sign;
    }
}

/*
 * Literal helper functions.
 */
function literalGetIdx(literal)
{
    return (literal < 0? -literal: literal);
}
function literalGetSign(literal)
{
    return (literal < 0);
}
function literalGetVar(state, literal)
{
    var idx = literalGetIdx(literal);
    return state.vars[idx];
}
function literalIsFalse(state, literal)
{
    var v = literalGetVar(state, literal);
    return (v.set && v.sign != literalGetSign(literal));
}
function literalGetMark(state, literal)
{
    var v = literalGetVar(state, literal);
    return v.mark;
}
function literalAddWatch(state, literal, clause)
{
    var v = literalGetVar(state, literal);
    var watch = v.watches[Number(literalGetSign(literal))];
    watch.push(clause);
}
function literalSet(state, literal, reason)
{
    var v = literalGetVar(state, literal);
    v.sign = literalGetSign(literal);
    v.set = true;
    v.dlevel = state.dlevel;
    v.reason = reason;
    state.trail.push(literal);
}

/*
 * Add a new clause.
 */
function satAddClause(state, clause)
{
    switch (clause.length)
    {
        case 0:
            // Empty clause:
            state.empty = true;
            return;

        case 1:
            var v = literalGetVar(state, clause[0]);
            var sign = literalGetSign(clause[0]);
            if (v.unit)
            {
                if (sign != v.unit_sign)
                    state.empty = true;
                return;
            }
            v.setUnit(sign);
            return;

        default:

            literalAddWatch(state, clause[0], clause);
            literalAddWatch(state, clause[1], clause);
    }
}

/*
 * Select a literal.  Chooses a literal at random (provided not already set).
 */
function satSelectLiteral(state)
{
    var M = 1, N = state.vars.length-1;
    var i = Math.floor(M + (1+N-M)*Math.random())
    var i0 = i;

    while (state.vars[i].set)
    {
        i++;
        if (i >= state.vars.length)
            i = 1;
        if (i == i0)
            return 0; 
    }

    var literal = (Math.random() < 0.5? -i: i);
    return literal; 
}

/*
 * Solver main loop.
 */
function satSolve(size, clauses)
{
    // Create the state:
    var state = new State();
    for (var i = 0; i < size; i++)
        state.vars.push(new Variable());
    for (var i = 0; i < clauses.length; i++)
        satAddClause(state, clauses[i]);

    // UNSAT if empty clause has been asserted:
    if (state.empty)
        return false;

    // Find and propagate unit clauses:
    for (var i = 1; i < state.vars.length; i++)
    {
        var v = state.vars[i];
        if (v.unit)
        {
            var literal = (v.unit_sign? -i: i);
            if (!satUnitPropagate(state, literal, null))
                return false;
        }
    }

    // Main loop:
    for (state.dlevel = 1; true; state.dlevel++)
    {
        var literal = satSelectLiteral(state);
        if (literal == 0)
        {
            // All variables are now set; and no conflicts; therefore SAT
            return true;
        }
        if (!satUnitPropagate(state, literal, null))
        {
            // UNSAT
            return false;
        }
    }

    return true;
}

/*
 * Unit propagation.
 */
function satUnitPropagate(state, literal, reason)
{
    var curr, next;
    var restart;

    do
    {
        curr = state.trail.length;
        next = curr + 1;

        literalSet(state, literal, reason);

        restart = false;
        while (curr < next)
        {
            literal = state.trail[curr];
            curr++;
            literal = -literal;
            var v = literalGetVar(state, literal);
            var watch = v.watches[Number(literalGetSign(literal))];
            for (var i = 0; i < watch.length; i++)
            {
                var clause = watch[i];
                var watch_idx = Number(clause[0] == literal);
                var watch_lit = clause[watch_idx];
                var watch_sign = literalGetSign(watch_lit);
                var w = literalGetVar(state, watch_lit);
                if (w.set && w.sign == watch_sign)
                {
                    // 'clause' is true -- no work to do.
                    continue;
                }

                // Search for a non-false literal in 'clause'.
                var j;
                for (j = 2; j < clause.length &&
                        literalIsFalse(state, clause[j]); j++)
                    ;
 
                if (j >= clause.length)
                {
                    // All other literals a false; use the other watch:
                    if (!w.set)
                    {
                        // Implied set:
                        if (watch_idx != 0)
                        {
                            clause[0] = watch_lit;
                            clause[1] = literal;
                        }
                        literalSet(state, watch_lit, clause);
                        next++;
                        continue;
                    }

                    // All literals in 'clause' are false; conflict!
                    reason = satBacktrack(state, clause);
                    if (reason == null)
                        return false;
                    literal = reason[0];
                    restart = true;
                    break;
                }

                // Watch the other literal:
                var new_lit = clause[j];
                clause[Number(!watch_idx)] = new_lit;
                clause[j] = literal;
                literalAddWatch(state, new_lit, clause);
                if (i == watch.length-1)
                    watch.pop();
                else
                {
                    watch[i] = watch.pop();
                    i--;
                }
            }

            if (restart)
                break;
        }
    }
    while (restart);

    return true;
}

/*
 * Backtracking and no-good learning.
 */
function satBacktrack(state, reason)
{
    var conflicts = [];

    // Level 0 failure; no work to do.
    if (state.dlevel == 0)
        return null;

    // Mark literals in reason:
    var count = 0;
    for (var i = 0; i < reason.length; i++)
    {
        var v = literalGetVar(state, reason[i]);
        if (v.dlevel == 0)
            continue;
        v.mark = true;
        if (v.dlevel < state.dlevel)
            conflicts.push(reason[i]);
        else
            count++;
    }

    // Find the UIP and collect conflicts:
    var tlevel = state.trail.length-1;
    var literal;
    do
    {
        if (tlevel < 0)
            return null;
        literal = state.trail[tlevel--];
        var v = literalGetVar(state, literal);
        v.set = false;
        if (!v.mark)
            continue;
        v.mark = false;
        count--;
        if (count <= 0)
            break;
        for (var i = 1; i < v.reason.length; i++)
        {
            literal = v.reason[i];
            var w = literalGetVar(state, literal);
            if (w.mark || w.dlevel == 0)
                continue;
            if (w.dlevel < state.dlevel)
                conflicts.push(literal);
            else
                count++;
            w.mark = true;
        }
    }
    while (true);

    // Simplify the conflicts; create the no-good.
    var nogood = [-literal];
    var blevel = 0;
    for (var i = 0; i < conflicts.length; i++)
    {
        literal = conflicts[i];
        v = literalGetVar(state, literal);
        if (v.reason != null)
        {
            var k;
            for (k = 1; k < v.reason.length &&
                    literalGetMark(state, v.reason[k]); k++)
                ;
            if (k >= v.reason.length)
                continue;
        }
        nogood.push(literal);
        if (blevel < v.dlevel)
        {
            blevel = v.dlevel;
            nogood[nogood.length-1] = nogood[1];
            nogood[1] = literal;
        }
    }

    // Unwind the trail:
    while (tlevel >= 0)
    {
        literal = state.trail[tlevel];
        v = literalGetVar(state, literal);
        if (v.dlevel <= blevel)
            break;
        v.set = false;
        tlevel--;
    }
    state.trail.length = tlevel+1;

    // Clear the marks:
    for (var i = 0; i < conflicts.length; i++)
    {
        v = literalGetVar(state, conflicts[i]);
        v.mark = false;
    }

    // Add the no-good clause:
    satAddClause(state, nogood);
    state.dlevel = blevel;
    if (state.empty)
        return null;

    return nogood;
}
