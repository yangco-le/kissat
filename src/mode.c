#include "bump.h"
#include "inline.h"
#include "inlineheap.h"
#include "inlinequeue.h"
#include "print.h"
#include "reluctant.h"
#include "rephase.h"
#include "report.h"
#include "restart.h"
#include "resources.h"

#include <inttypes.h>
#include <math.h>

void
kissat_init_mode_limit (kissat * solver)
{
  limits *limits = &solver->limits;

  if (GET_OPTION (stable) == 1)
    {
      assert (!solver->stable);

      const uint64_t conflicts_delta = GET_OPTION (modeinit);
      const uint64_t conflicts_limit = CONFLICTS + conflicts_delta;
      assert (conflicts_limit);
      limits->mode.conflicts = conflicts_limit;
      limits->mode.ticks = 0;

      kissat_very_verbose (solver, "initial stable mode switching limit "
			   "at %s after %s conflicts",
			   FORMAT_COUNT (conflicts_limit),
			   FORMAT_COUNT (conflicts_delta));

      solver->mode.ticks = solver->statistics.search_ticks;
#ifndef QUIET
      solver->mode.conflicts = CONFLICTS;
#ifdef METRICS
      solver->mode.propagations = solver->statistics.search_propagations;
#endif
// *INDENT-OFF*
      solver->mode.entered = kissat_process_time ();
      kissat_very_verbose (solver,
        "starting focused mode at %.2f seconds "
        "(%" PRIu64 " conflicts, %" PRIu64 " ticks"
#ifdef METRICS
	", %" PRIu64 " propagations, %" PRIu64 " visits"
#endif
	")",
        solver->mode.entered, solver->mode.conflicts, solver->mode.ticks
#ifdef METRICS
        , solver->mode.propagations, solver->mode.visits
#endif
	);
// *INDENT-ON*
#endif
    }
  else
    kissat_very_verbose (solver,
			 "no need to set mode limit (only %s mode enabled)",
			 GET_OPTION (stable) ? "stable" : "focused");
}

static void
update_mode_limit (kissat * solver)
{
  kissat_init_averages (solver, &AVERAGES);

  limits *limits = &solver->limits;
  statistics *statistics = &solver->statistics;

  assert (GET_OPTION (stable) == 1);

  if (limits->mode.conflicts)
    {
      assert (solver->stable);
      assert (solver->mode.ticks <= statistics->search_ticks);
      limits->mode.interval = statistics->search_ticks - solver->mode.ticks;
      limits->mode.conflicts = 0;
    }

  const uint64_t interval = limits->mode.interval;
  assert (interval > 0);

  const uint64_t count = (statistics->switched_modes + 1) / 2;
  const uint64_t scaled = interval * kissat_nlogpown (count, 4);
  limits->mode.ticks = statistics->search_ticks + scaled;
#ifndef QUIET
  if (solver->stable)
    kissat_phase (solver, "stable", GET (stable_modes),
		  "new focused mode switching limit of %s after %s ticks",
		  FORMAT_COUNT (limits->mode.ticks), FORMAT_COUNT (scaled));
  else
    kissat_phase (solver, "focus", GET (focused_modes),
		  "new stable mode switching limit of %s after %s ticks",
		  FORMAT_COUNT (limits->mode.ticks), FORMAT_COUNT (scaled));

  solver->mode.conflicts = statistics->conflicts;
#ifdef METRICS
  solver->mode.propagations = statistics->search_propagations;
#endif
#endif
  solver->mode.ticks = statistics->search_ticks;
}

static void
report_switching_from_mode (kissat * solver)
{
#ifndef QUIET
  if (kissat_verbosity (solver) < 2)
    return;

  const double current_time = kissat_process_time ();
  const double delta_time = current_time - solver->mode.entered;

  statistics *statistics = &solver->statistics;

  const uint64_t delta_conflicts =
    statistics->conflicts - solver->mode.conflicts;

  const uint64_t delta_ticks = statistics->search_ticks - solver->mode.ticks;
#ifdef METRICS
  const uint64_t delta_propagations =
    statistics->search_propagations - solver->mode.propagations;
#endif
  solver->mode.entered = current_time;

  // *INDENT-OFF*
  kissat_very_verbose (solver, "%s mode took %.2f seconds "
    "(%s conflicts, %s ticks"
#ifdef METRICS
    ", %s propagations"
#endif
    ")", solver->stable ? "stable" : "focused",
    delta_time, FORMAT_COUNT (delta_conflicts), FORMAT_COUNT (delta_ticks)
#ifdef METRICS
    , FORMAT_COUNT (delta_propagations)
#endif
    );
  // *INDENT-ON*
#else
  (void) solver;
#endif
}

static void
switch_to_focused_mode (kissat * solver)
{
  assert (solver->stable);
  report_switching_from_mode (solver);
  REPORT (0, ']');
  STOP (stable);
  INC (focused_modes);
  kissat_phase (solver, "focus", GET (focused_modes),
		"switching to focused mode after %s conflicts",
		FORMAT_COUNT (CONFLICTS));
  solver->stable = false;
  update_mode_limit (solver);
  START (focused);
  REPORT (0, '{');
  kissat_reset_search_of_queue (solver);
  kissat_update_focused_restart_limit (solver);
}

static void
switch_to_stable_mode (kissat * solver)
{
  assert (!solver->stable);
  report_switching_from_mode (solver);
  REPORT (0, '}');
  STOP (focused);
  INC (stable_modes);
  solver->stable = true;
  kissat_phase (solver, "stable", GET (stable_modes),
		"switched to stable mode after %" PRIu64
		" conflicts", CONFLICTS);
  update_mode_limit (solver);
  START (stable);
  REPORT (0, '[');
  kissat_init_reluctant (solver);
  kissat_update_scores (solver);
}

// bool
// kissat_switching_search_mode (kissat * solver)
// {
//   assert (!solver->inconsistent);

//   if (GET_OPTION (stable) != 1)
//     return false;

//   limits *limits = &solver->limits;
//   statistics *statistics = &solver->statistics;

//   if (limits->mode.conflicts)
//     {
//       assert (!solver->stable);
//       assert (!statistics->switched_modes);
//       return statistics->conflicts >= limits->mode.conflicts;
//     }

//   return statistics->search_ticks >= limits->mode.ticks;
// }

void
kissat_switch_search_mode (kissat * solver)
{

  assert (!solver->inconsistent);

  if (GET_OPTION (stable) != 1)
    return;

  limits *limits = &solver->limits;
  statistics *statistics = &solver->statistics;

  if (limits->mode.conflicts)
    {
      assert (!solver->stable);
      assert (!statistics->switched_modes);
      if (statistics->conflicts < limits->mode.conflicts) return;
    }
  else if (statistics->search_ticks < limits->mode.ticks) return;

  unsigned stable_restarts = 0; // 统计restart次数
	solver->mab_reward[solver->stable] += !solver->mab_chosen_tot? 0: log2(solver->mab_decisions) / solver->mab_chosen_tot; // reward更新
	for (all_variables (idx)) solver->mab_chosen[idx]=0;  // 重置对每个variable的统计
	solver->mab_chosen_tot = 0;  // 重置chosen_tot
	solver->mab_decisions = 0;  // 重置decisions
	for (unsigned i=0; i < solver->mab_num_arms; i++) stable_restarts +=  solver->mab_select[i];  // 统计restart次数

  unsigned curr_chosen = 0;  // 当前的策略选择
  if (stable_restarts < solver->mab_num_arms) {  // 每个arm没有都被选择过
		curr_chosen = solver->stable == 0? 1: 0; 
	} else {
		double ucb[2];  // 计算upper confidence bound
		for (unsigned i=0; i < solver->mab_num_arms; i++) {
		  ucb[i] = solver->mab_reward[i] / solver->mab_select[i] + sqrt(solver->mabc * log(stable_restarts+1) / solver->mab_select[i]);
		  if (i != 0 && ucb[i]>ucb[curr_chosen]) curr_chosen = i;  // 选择stable模式
	  }
  }

	solver->mab_select[curr_chosen]++;  // 统计选择次数
  if (curr_chosen == solver->stable) return;  // if mode unchanged, do nothing

  INC (switched_modes);

  if (solver->stable)
    switch_to_focused_mode (solver);
  else
    switch_to_stable_mode (solver);

  assert (!solver->limits.mode.conflicts);

  solver->averages[solver->stable].saved_decisions = DECISIONS;
}
