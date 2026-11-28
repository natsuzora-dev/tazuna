-module(tazuna_launch_ffi).
-export([argv/0, getenv/1, spawn/2, exit/1, platform/0, download/1, sha256/1, gunzip/1, pid/0]).

argv() ->
    [unicode:characters_to_binary(A) || A <- init:get_plain_arguments()].

getenv(Name) ->
    case os:getenv(unicode:characters_to_list(Name)) of
        false -> {error, nil};
        Value -> {ok, unicode:characters_to_binary(Value)}
    end.

spawn(Path, Args) ->
    Options = [{args, [unicode:characters_to_list(A) || A <- Args]},
               {line, 65536}, exit_status, binary, use_stdio],
    try open_port({spawn_executable, unicode:characters_to_list(Path)}, Options) of
        Port -> {ok, relay(Port, [])}
    catch
        error:Reason ->
            {error, unicode:characters_to_binary(io_lib:format("~p", [Reason]))}
    end.

%% Prints whole lines only, so a UTF-8 sequence split across reads stays intact.
relay(Port, Partial) ->
    receive
        {Port, {data, {noeol, Part}}} ->
            relay(Port, [Partial, Part]);
        {Port, {data, {eol, Line}}} ->
            io:put_chars([Partial, Line, $\n]),
            relay(Port, []);
        {Port, {exit_status, Status}} ->
            case iolist_size(Partial) of
                0 -> ok;
                _ -> io:put_chars(Partial)
            end,
            Status
    end.

exit(Code) ->
    erlang:halt(Code).

platform() ->
    Os = case os:type() of
             {unix, darwin} -> <<"darwin">>;
             {win32, _} -> <<"win32">>;
             {_, Name} -> atom_to_binary(Name)
         end,
    Arch = case os:type() of
               {win32, _} -> os:getenv("PROCESSOR_ARCHITECTURE", "");
               _ -> erlang:system_info(system_architecture)
           end,
    <<Os/binary, "-", (arch(string:lowercase(Arch)))/binary>>.

arch("x86_64" ++ _) -> <<"x64">>;
arch("amd64" ++ _) -> <<"x64">>;
arch("aarch64" ++ _) -> <<"arm64">>;
arch("arm64" ++ _) -> <<"arm64">>;
arch(Other) -> unicode:characters_to_binary(hd(string:split(Other, "-"))).

download(<<"file://", Path/binary>>) ->
    case file:read_file(Path) of
        {ok, Bits} -> {ok, Bits};
        {error, Reason} -> {error, atom_to_binary(Reason)}
    end;
download(Url) ->
    try
        {ok, _} = application:ensure_all_started(ssl),
        {ok, _} = application:ensure_all_started(inets),
        Ssl = [{verify, verify_peer}, {cacerts, public_key:cacerts_get()},
               {customize_hostname_check,
                [{match_fun, public_key:pkix_verify_hostname_match_fun(https)}]}],
        httpc:request(get, {unicode:characters_to_list(Url), [{"user-agent", "tazuna"}]},
                      [{ssl, Ssl}, {autoredirect, true}], [{body_format, binary}])
    of
        {ok, {{_, 200, _}, _, Body}} -> {ok, Body};
        {ok, {{_, Status, _}, _, _}} -> {error, <<"HTTP status ", (integer_to_binary(Status))/binary>>};
        {error, Reason} -> {error, describe(Reason)}
    catch
        Class:Reason -> {error, describe({Class, Reason})}
    end.

describe(Term) ->
    unicode:characters_to_binary(io_lib:format("~p", [Term])).

sha256(Bits) ->
    binary:encode_hex(crypto:hash(sha256, Bits), lowercase).

gunzip(Bits) ->
    try zlib:gunzip(Bits) of
        Out -> {ok, Out}
    catch
        _:Reason -> {error, describe(Reason)}
    end.

pid() ->
    list_to_integer(os:getpid()).
