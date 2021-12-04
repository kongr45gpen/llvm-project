#include <experimental/mirror>
#include <iostream>

enum class weekdays : int {
  monday, tuesday, wednesday, thursday, friday, saturday, sunday
};

static std::string_view enum_to_string(weekdays e) {
  return select(
    unpack(get_enumerators(mirror(weekdays))),
    [](auto& result, auto mo, auto e) {
      if (weekdays(get_constant(mo)) == e) {
        result = get_name(mo);
      }
    }, std::string_view{}, e);
}

static weekdays string_to_enum(std::string_view n) {
  return select(
    unpack(get_enumerators(mirror(weekdays))),
    [](auto& result, auto mo, auto n) {
      if (std::string_view{get_name(mo)} == n) {
        result = weekdays(get_constant(mo));
      }
    }, weekdays{}, n);
}

static void next_day(std::string_view n) {
  auto d = string_to_enum(n);
  std::cout << n 
            << " -> "
            << enum_to_string(weekdays((int(d) + 1) % 7))
            << std::endl;
}

int main() {
  using namespace std::experimental::mirror;
  for_each(unpack(get_enumerators(mirror(weekdays))), [](auto mo){
      next_day(get_name(mo));
    });

  return 0;
}
