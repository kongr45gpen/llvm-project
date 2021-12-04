#include <experimental/mirror>
#include <iostream>

enum class weekdays : int {
  monday, tuesday, wednesday, thursday, friday, saturday, sunday
};

template <typename E>
static std::string_view enum_to_string(E e) {
  return select(
    unpack(get_enumerators(mirror(weekdays))),
    [](auto& result, auto mo, auto e) {
      if (E(get_constant(mo)) == e) {
        result = get_name(mo);
      }
    }, std::string_view{}, e);
}

template <typename E>
static E string_to_enum(std::string_view n) {
  return select(
    unpack(get_enumerators(mirror(weekdays))),
    [](auto& result, auto mo, auto n) {
      if (std::string_view{get_name(mo)} == n) {
        result = E(get_constant(mo));
      }
    }, E{}, n);
}

static void next_day(std::string_view n) {
  auto d = string_to_enum<weekdays>(n);
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
