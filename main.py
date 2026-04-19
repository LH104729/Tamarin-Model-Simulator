import argparse
from src.simulator import Simulator, simulator_from_path
from src.base_types import Term, Fact, RewriteRule
from textual.app import App, ComposeResult, Binding
from textual.containers import Container, Horizontal, VerticalScroll
from textual.widgets import (
  Footer,
  Rule,
  Static,
  ListView,
  ListItem,
  Select,
  Input,
  TabbedContent,
  TabPane,
)

from textual.screen import Screen
from textual.reactive import reactive


class RuleApplyScreen(Screen):
  BINDINGS = [
    Binding(key="backspace", action="back()", description="Back"),
    Binding(key="c", action="clear()", description="Clear selections"),
    Binding(key="enter", action="apply()", description="Apply Rule"),
  ]
  CSS = """
  Select.hide {
      visibility: hidden;
      height: 0;
  }
  """
  possible_facts: reactive[dict[Fact, set[Fact]]] = reactive(
    dict[Fact, set[Fact]], recompose=True
  )
  status: reactive[str] = reactive("", recompose=True)
  input_placeholder: reactive[str] = reactive("")

  def __init__(self, rule: RewriteRule, simulator: Simulator, callback=None):
    super().__init__()
    self.rule = rule
    self.simulator = simulator
    self.possible_facts = self.simulator.get_rule_possible_values(self.rule.name)
    self.selected_values: dict[Term, Term] = {}
    self.public_assignments: dict[Term, Term] = {}
    self.callback = callback

  def compose(self):
    with Container():
      with VerticalScroll():
        yield Static(
          f"[bold]Apply Rule:[\bold] {self.rule.name}", id="rule_detail_title"
        )
        yield Static(f"[bold]Status:[\bold] {self.status}", id="rule_status")
        yield Rule()
        yield Static("[bold]Premises:[\bold]")
        for i, p in enumerate(self.rule.premises):
          yield Static(str(p))
          yield Select(
            ((str(fact), fact) for fact in self.possible_facts[p]),
            value=self.selected_values.get(
              p,
              Select.NULL
              if len(self.possible_facts[p]) != 1
              else next(iter(self.possible_facts[p])),
            ),
            id=f"premise_select_{i}",
            classes="hide" if p.name == "Fr" else "show",
          )
        for i, p in enumerate(self.rule.required_public_terms):
          yield Static(f"Required public term: {p}")
          yield Input(
            placeholder=self.input_placeholder,
            type="text",
            id=f"public_input_{i}",
          )
        yield Rule()
        yield Static("[bold]Actions:[\bold]")
        for a in self.rule.actions:
          yield Static(str(a))
        yield Rule()
        yield Static("[bold]Conclusion:[\bold]")
        for c in self.rule.conclusion:
          yield Static(str(c))
    yield Footer()

  def on_select_changed(self, event):
    if event.select.id.startswith("premise_select_"):
      i = int(event.select.id.split("_")[-1])
      p = self.rule.premises[i]
      if event.value == self.selected_values.get(p, Select.NULL):
        return
      if event.value is not Select.NULL:
        self.selected_values[p] = event.value
      else:
        self.selected_values.pop(p, None)
      self.possible_facts = self.simulator.get_rule_possible_values(
        self.rule.name, self.selected_values
      )
      self.mutate_reactive(RuleApplyScreen.possible_facts)

  def on_input_changed(self, event):
    if event.input.id.startswith("public_input_"):
      i = int(event.input.id.split("_")[-1])
      p = self.rule.required_public_terms[i]
      value_str = event.value.strip()
      if value_str == "":
        self.public_assignments.pop(p, None)
      else:
        self.public_assignments[p] = Term(
          f"'{value_str}'", sort=p.sort, is_constant=True
        )

  def action_clear(self):
    self.selected_values = {}
    self.possible_facts = self.simulator.get_rule_possible_values(self.rule.name)

    self.mutate_reactive(RuleApplyScreen.possible_facts)
    self.mutate_reactive(RuleApplyScreen.input_placeholder)

  def action_back(self):
    self.app.pop_screen()

  def action_apply(self):
    renaming_map: dict[Term, Term] | None = self.simulator.can_apply_rule(
      self.rule.name, self.selected_values, self.public_assignments
    )
    if renaming_map is not None and self.simulator.apply_rule(
      self.rule.name, renaming_map
    ):
      self.app.pop_screen()
      if self.callback is not None:
        self.callback()
    else:
      self.status = "Cannot apply rule with the selected facts"
      self.mutate_reactive(RuleApplyScreen.status)


class TamarinModelSimulator(App):
  BINDINGS = [
    Binding(key="q", action="quit", description="Quit"),
    Binding(key="u", action="undo()", description="Undo"),
    Binding(key="U", action="redo()", description="Redo"),
  ]
  simulator: reactive[Simulator] = reactive(Simulator, recompose=True)

  def __init__(self, simulator: Simulator):
    super().__init__()
    self.simulator = simulator
    self.rule_names = list(self.simulator.rule_names)
    self.attacker_rule_names = list(self.simulator.attacker_rule_names)
    self.selected_tabs = {
      "state_tabs": "state_tab",
      "rules_tabs": "rules_tab",
    }

  def compose(self) -> ComposeResult:
    with Horizontal():
      with Container():
        with TabbedContent(
          initial=self.selected_tabs.get("rules_tabs"), id="rules_tabs"
        ):
          with TabPane("Rules", id="rules_tab"):
            yield ListView(
              *[ListItem(Static(r), name=r) for r in self.rule_names],
              id="rules_list",
            )
          with TabPane("KU/KD Rules", id="k_rules_tab"):
            yield ListView(
              *[ListItem(Static(r), name=r) for r in self.attacker_rule_names],
              id="attacker_rules_list",
            )
      with Container():
        with Container():
          with TabbedContent(
            initial=self.selected_tabs.get("state_tabs"), id="state_tabs"
          ):
            with TabPane("State", id="state_tab"):
              with ListView():
                for fact, count in self.simulator.state.state.items():
                  if fact.name not in ["Out", "In", "KU", "KD"]:
                    yield ListItem(
                      Static(f"{fact} (x{count})" if count > 1 else str(fact)),
                      name=str(fact),
                    )
            with TabPane("In/Out", id="io_tab"):
              with ListView():
                for fact, count in self.simulator.state.state.items():
                  if fact.name in ["Out", "In"]:
                    yield ListItem(
                      Static(f"{fact} (x{count})" if count > 1 else str(fact)),
                      name=str(fact),
                    )
            with TabPane("KU/KD", id="k_tab"):
              with ListView():
                for fact, count in self.simulator.state.state.items():
                  if fact.name in ["KU", "KD"]:
                    yield ListItem(
                      Static(f"{fact} (x{count})" if count > 1 else str(fact)),
                      name=str(fact),
                    )
        with Container():
          yield Static("Trace:", id="trace_title")
          with ListView(id="trace_list"):
            for idx, facts in enumerate(
              reversed(self.simulator.state.trace[: self.simulator.state.time])
            ):
              if len(facts) != 0:
                yield ListItem(
                  Static(f"--- Time {self.simulator.state.time - idx} ---"),
                  name=f"time_{self.simulator.state.time - idx}",
                )
                for fact in facts:
                  yield ListItem(Static(str(fact)), name=str(fact))
    yield Footer()

  def recompose_simulator(self):
    self.mutate_reactive(TamarinModelSimulator.simulator)

  def on_list_view_selected(self, event):
    if (
      event.list_view.id == "rules_list" or event.list_view.id == "attacker_rules_list"
    ):
      rule_name = event.item.name
      rule = self.simulator.rules[rule_name]
      self.app.push_screen(
        RuleApplyScreen(rule, self.simulator, self.recompose_simulator)
      )

  def on_tabbed_content_tab_activated(self, event):
    self.selected_tabs[event.tabbed_content.id] = event.tabbed_content.get_pane(
      event.tab
    ).id

  def action_undo(self):
    self.simulator.state.undo()
    self.recompose_simulator()

  def action_redo(self):
    self.simulator.state.redo()
    self.recompose_simulator()


def parse_args():
  parser = argparse.ArgumentParser(description="Tamarin Model Simulator")
  parser.add_argument("model_file", type=str, help="Path to the Tamarin model file")
  return parser.parse_args()


def main():
  args = parse_args()
  simulator: Simulator = simulator_from_path(args.model_file)
  app = TamarinModelSimulator(simulator)
  app.run()


if __name__ == "__main__":
  main()
