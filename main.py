import argparse
from src.simulator import Simulator, simulator_from_path
from src.base_types import Term, Fact, RewriteRule
from textual.app import App, ComposeResult, Binding
from textual.containers import Container, Horizontal
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

from textual.reactive import reactive


class TamarinModelSimulator(App):
  BINDINGS = [
    Binding(key="ctrl+q", action="quit", description="Quit"),
    Binding(key="u", action="undo()", description="Undo"),
    Binding(key="U", action="redo()", description="Redo"),
    Binding(key="c", action="clear()", description="Clear selections"),
    Binding(key="enter", action="apply()", description="Apply Rule"),
  ]
  CSS = """
  #status-container {
    height: 3;
    padding-top: 0;
    padding-left: 1;
    padding-right: 1;
    padding-bottom: 1;
  }
  .box {
    # border: solid white;
    padding: 1;
    margin: 0;
  }
  .height-auto {
    height: auto;
  }
  .overflow-auto {
    overflow: auto;
  }
  .hide {
    display: none;
  }
  ListView:disabled {
    opacity: 100% !important;
  }
  """
  simulator: reactive[Simulator] = reactive(Simulator, recompose=True)
  status: reactive[str] = reactive("", recompose=True)

  input_placeholder: reactive[str] = reactive("")
  selected_rule: reactive[RewriteRule | None] = reactive(
    RewriteRule | None, recompose=True
  )
  possible_facts: reactive[dict[Fact, set[Fact]]] = reactive(
    dict[Fact, set[Fact]], recompose=True
  )

  rule_names: list[str]
  attacker_rule_names: list[str]
  selected_tabs: dict[str, str] = {
    "state_tabs": "state_tab",
    "rules_tabs": "rules_tab",
  }

  selected_values: dict[Term, Term] = {}
  public_assignments: dict[Term, Term] = {}

  def __init__(self, simulator: Simulator):
    super().__init__()
    self.simulator = simulator
    self.selected_rule = None
    self.rule_names = list(self.simulator.rule_names)
    self.attacker_rule_names = list(self.simulator.attacker_rule_names)

  def compose(self) -> ComposeResult:
    yield Footer()
    with Horizontal():
      with Container():
        with Container(classes="box"):
          with TabbedContent(
            initial=self.selected_tabs.get("rules_tabs"), id="rules_tabs"
          ) as t:
            t.focus()
            with TabPane("Rules", id="rules_tab"):
              with Container(classes="overflow-auto"):
                yield ListView(
                  *[ListItem(Static(r), name=r) for r in self.rule_names],
                  id="rules_list",
                )
            with TabPane("KU/KD Rules", id="k_rules_tab"):
              with Container(classes="overflow-auto"):
                yield ListView(
                  *[ListItem(Static(r), name=r) for r in self.attacker_rule_names],
                  id="attacker_rules_list",
                )
            with TabPane("Apply", id="apply_tab"):
              with Container(classes="overflow-auto"):
                if self.selected_rule is not None:
                  yield Static(
                    f"[bold]Apply Rule:[\bold] {self.selected_rule.name}",
                    id="rule_detail_title",
                  )
                  yield Rule()
                  yield Static("[bold]Premises:[\bold]")
                  for i, p in enumerate(self.selected_rule.premises):
                    yield Static(str(p))
                    yield Select(
                      (
                        (str(fact), fact)
                        for fact in sorted(self.possible_facts.get(p, []), key=str)
                      ),
                      value=self.selected_values.get(
                        p,
                        Select.NULL
                        if len(self.possible_facts.get(p, [])) != 1
                        else next(iter(self.possible_facts.get(p, []))),
                      ),
                      id=f"premise_select_{i}",
                      classes="hide" if p.name == "Fr" else "show",
                    )
                  for i, p in enumerate(self.selected_rule.required_public_terms):
                    yield Static(f"Public term: {p}")
                    yield Input(
                      placeholder=self.input_placeholder,
                      type="text",
                      id=f"public_input_{i}",
                    )
                  yield Rule()
                  yield Static("[bold]Actions:[\bold]")
                  for a in self.selected_rule.actions:
                    yield Static(str(a))
                  yield Rule()
                  yield Static("[bold]Conclusion:[\bold]")
                  for c in self.selected_rule.conclusion:
                    yield Static(str(c))
                else:
                  yield Static("No rule selected.")
        with Container(id="status-container"):
          with Container(classes="overflow-auto"):
            yield Static(f"[bold]Status:[\bold] {self.status}", id="rule_status")
      with Container():
        with Container(classes="box"):
          with TabbedContent(
            initial=self.selected_tabs.get("state_tabs"), id="state_tabs"
          ):
            with TabPane("State", id="state_tab"):
              with Container(classes="overflow-auto", disabled=True):
                with ListView(initial_index=None):
                  for fact, count in reversed(self.simulator.state.state.items()):
                    if fact.name not in ["Out", "In", "KU", "KD"]:
                      yield ListItem(
                        Static(f"{fact} (x{count})" if count > 1 else str(fact)),
                        name=str(fact),
                        disabled=True,
                      )
            with TabPane("In/Out", id="io_tab"):
              with Container(classes="overflow-auto", disabled=True):
                with ListView(initial_index=None):
                  for fact, count in reversed(self.simulator.state.state.items()):
                    if fact.name in ["Out", "In"]:
                      yield ListItem(
                        Static(f"{fact} (x{count})" if count > 1 else str(fact)),
                        name=str(fact),
                        disabled=True,
                      )
            with TabPane("KU/KD", id="k_tab"):
              with Container(classes="overflow-auto", disabled=True):
                with ListView(initial_index=None):
                  for fact, count in reversed(self.simulator.state.state.items()):
                    if fact.name in ["KU", "KD"]:
                      yield ListItem(
                        Static(f"{fact} (x{count})" if count > 1 else str(fact)),
                        name=str(fact),
                        disabled=True,
                      )
        with Container(classes="box"):
          with TabbedContent():
            with TabPane("Trace"):
              with Container(classes="overflow-auto", disabled=True):
                with ListView(initial_index=None):
                  for idx, facts in enumerate(
                    reversed(self.simulator.state.trace[: self.simulator.state.time])
                  ):
                    if len(facts) != 0:
                      yield ListItem(
                        Static(f"--- Time {self.simulator.state.time - idx} ---"),
                        name=f"time_{self.simulator.state.time - idx}",
                        disabled=True,
                      )
                      for fact in facts:
                        yield ListItem(Static(str(fact)), name=str(fact), disabled=True)

  def recompose_simulator(self):
    self.mutate_reactive(TamarinModelSimulator.simulator)
    self.query_one("#state_tabs", TabbedContent).focus()

  def on_list_view_selected(self, event):
    if (
      event.list_view.id == "rules_list" or event.list_view.id == "attacker_rules_list"
    ):
      selected_rule = self.simulator.rules[event.item.name]
      self.possible_facts, self.status = self.simulator.get_rule_possible_values(
        selected_rule.name
      )
      self.selected_values = {}
      self.public_assignments = {}
      self.selected_rule = selected_rule

      self.selected_tabs["rules_tabs"] = "apply_tab"
      self.query_one("#rules_tabs", TabbedContent).active = "apply_tab"
      self.query_one("#rules_tabs", TabbedContent).focus()

  def on_select_changed(self, event):
    if event.select.id.startswith("premise_select_"):
      i = int(event.select.id.split("_")[-1])
      p = self.selected_rule.premises[i]
      if event.value == self.selected_values.get(p, Select.NULL):
        return
      if event.value is not Select.NULL:
        self.selected_values[p] = event.value
      else:
        self.selected_values.pop(p, None)
      self.possible_facts, self.status = self.simulator.get_rule_possible_values(
        self.selected_rule.name, self.selected_values
      )
      self.mutate_reactive(TamarinModelSimulator.possible_facts)

  def on_tabbed_content_tab_activated(self, event: TabbedContent.TabActivated):
    self.selected_tabs[event.tabbed_content.id] = event.pane.id

  def action_clear(self):
    if self.selected_rule is None:
      return
    self.selected_values = {}
    self.possible_facts, self.status = self.simulator.get_rule_possible_values(
      self.selected_rule.name
    )

    self.mutate_reactive(TamarinModelSimulator.possible_facts)
    self.mutate_reactive(TamarinModelSimulator.input_placeholder)

  def action_apply(self):
    if self.selected_rule is None:
      return
    renaming_map: dict[Term, Term] | None = self.simulator.can_apply_rule(
      self.selected_rule.name, self.selected_values, self.public_assignments
    )
    if renaming_map is not None and self.simulator.apply_rule(
      self.selected_rule.name, renaming_map
    ):
      self.selected_rule = None
      self.selected_values = {}
      self.selected_tabs["rules_tabs"] = "rules_tab"
      self.query_one("#rules_tabs", TabbedContent).active = "rules_tab"
      self.status = "Rule applied successfully"
    else:
      self.status = "Cannot apply rule with the selected facts."
      self.mutate_reactive(TamarinModelSimulator.status)

  def action_undo(self):
    if self.simulator.state.undo():
      self.status = "Undid last action."
      self.action_clear()
      self.mutate_reactive(TamarinModelSimulator.status)
      self.recompose_simulator()
    else:
      self.status = "No actions to undo."
      self.mutate_reactive(TamarinModelSimulator.status)

  def action_redo(self):
    if self.simulator.state.redo():
      self.status = "Redid last undone action."
      self.action_clear()
      self.mutate_reactive(TamarinModelSimulator.status)
      self.recompose_simulator()
    else:
      self.status = "No actions to redo."
      self.mutate_reactive(TamarinModelSimulator.status)


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
